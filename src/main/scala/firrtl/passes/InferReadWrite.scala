/*
Copyright (c) 2014 - 2016 The Regents of the University of
California (Regents). All Rights Reserved.  Redistribution and use in
source and binary forms, with or without modification, are permitted
provided that the following conditions are met:
   * Redistributions of source code must retain the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer.
   * Redistributions in binary form must reproduce the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer in the documentation and/or other materials
     provided with the distribution.
   * Neither the name of the Regents nor the names of its contributors
     may be used to endorse or promote products derived from this
     software without specific prior written permission.
IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.
*/

package firrtl.passes

import com.typesafe.scalalogging.LazyLogging

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.PrimOps._
import Annotations._

case class InferReadWriteAnnotation(t: String, tID: TransID)
    extends Annotation with Loose with Unstable {
  val target = CircuitName(t)
  def duplicate(n: Named) = this.copy(t=n.name)
}

// This pass examine the enable signals of the read & write ports of memories
// whose readLatency is greater than 1 (usually SeqMem in Chisel).
// If any product term of the enable signal of the read port is the complement
// of any product term of the enable signal of the write port, then the readwrite
// port is inferred.
object InferReadWritePass extends Pass {
  import collection.mutable.{ArrayBuffer, HashSet}
  import WrappedExpression.weq
  import Utils.{zero, one, BoolType}
  import MemPortUtils.memPortField
  import AnalysisUtils.{Connects, getConnects, getConnectOrigin}

  def name = "Infer ReadWrite Ports"
  implicit def expToString(e: Expression) = e.serialize

  def getProductTerms(connects: Connects)(e: Expression): Seq[Expression] = e match {
    // No ConstProp yet...
    case Mux(cond, tval, fval, _) if weq(tval, one) && weq(fval, zero) =>
      cond +: getProductTerms(connects)(connects(cond))
    // Visit each term of AND operation
    case DoPrim(And, args, consts, tpe) =>
      e +: (args flatMap getProductTerms(connects))
    // Visit connected nodes to references
    case _: WRef | _: WSubField | _: WSubIndex =>
      e +: (connects get e match {
        case None => Nil
        case Some(ex) => getProductTerms(connects)(ex)
      })
    // Otherwise just return itselt
    case _ => Seq(e)
  }

  def checkComplement(a: Expression, b: Expression) = (a, b) match {
    // b ?= Not(a)
    case (_, DoPrim(Not, args, _, _)) => weq(args.head, a)
    // a ?= Not(b)
    case (DoPrim(Not, args, _, _), _) => weq(args.head, b)
    // b ?= Eq(a, 0) or b ?= Eq(0, a)
    case (_, DoPrim(Eq, args, _, _)) =>
      weq(args(0), a) && weq(args(1), zero) ||
      weq(args(1), a) && weq(args(0), zero)
    // a ?= Eq(b, 0) or b ?= Eq(0, a)
    case (DoPrim(Eq, args, _, _), _) =>
      weq(args(0), b) && weq(args(1), zero) ||
      weq(args(1), b) && weq(args(0), zero)
    case _ => false
  }

  type Statements = collection.mutable.ArrayBuffer[Statement]
  def inferReadWriteStmt(connects: Connects, repl: Connects, stmts: Statements)(s: Statement): Statement =
    s map inferReadWriteStmt(connects, repl, stmts) match {
      // infer readwrite ports only for non combinational memories
      case mem: DefMemory if mem.readLatency > 0 =>
        val ut = UnknownType
        val ug = UNKNOWNGENDER
        val readers = HashSet[String]()
        val writers = HashSet[String]()
        val readwriters = ArrayBuffer[String]()
        for (w <- mem.writers ; r <- mem.readers) {
          val rclk = memPortField(mem, r, "clk")
          val wclk = memPortField(mem, w, "clk")
          val ren = memPortField(mem, r, "en")
          val wen = memPortField(mem, w, "en")
          val wp = getProductTerms(connects)(wen)
          val rp = getProductTerms(connects)(ren)
          // TODO: compare two clks
          if (wp exists (a => rp exists (b => checkComplement(a, b)))) {
            val allPorts = (mem.readers ++ mem.writers ++ mem.readwriters ++ readwriters).toSet
            // Uniquify names by examining all ports of the memory
            val rw = (for {
                idx <- Stream from 0
                newName = s"rw_$idx"
                if !allPorts(newName)
              } yield newName).head
            val rwExp = WSubField(WRef(mem.name, ut, MemKind, ug), rw, ut, ug)
            val raddr = memPortField(mem, r, "addr")
            val rdata = memPortField(mem, r, "data")
            val waddr = memPortField(mem, w, "addr")
            val wdata = memPortField(mem, w, "data")
            val wmask = memPortField(mem, w, "mask")
            readwriters += rw
            readers += r
            writers += w
            repl(rclk) = EmptyExpression
            repl(ren) = EmptyExpression
            repl(raddr) = EmptyExpression
            repl(rdata) = WSubField(rwExp, "rdata", mem.dataType, MALE)
            repl(wclk) = WSubField(rwExp, "clk", ClockType, FEMALE)
            repl(wen) = WSubField(rwExp, "wmode", BoolType, FEMALE)
            repl(waddr) = EmptyExpression
            repl(wdata) = WSubField(rwExp, "wdata", mem.dataType, FEMALE)
            repl(wmask) = WSubField(rwExp, "wmask", wmask.tpe, FEMALE)
            val en = DoPrim(Or, Seq(ren, wen), Nil, BoolType)
            val addr = Mux(wen, connects(waddr), connects(raddr), waddr.tpe)
            stmts ++= Seq(
              Connect(NoInfo, WSubField(rwExp, "en", BoolType, FEMALE), en),
              Connect(NoInfo, WSubField(rwExp, "addr", addr.tpe, FEMALE), addr)
            )
          }
        }
        if (readwriters.isEmpty) mem else DefMemory(mem.info,
          mem.name, mem.dataType, mem.depth, mem.writeLatency, mem.readLatency,
          mem.readers filterNot readers, mem.writers filterNot writers,
          mem.readwriters ++ readwriters)
      case s => s
    }

  def replaceExp(repl: Connects)(e: Expression): Expression =
    e map replaceExp(repl) match {
      case e: WSubField => repl getOrElse (e, e)
      case e => e
    }

  def replaceStmt(repl: Connects)(s: Statement): Statement =
    s map replaceStmt(repl) map replaceExp(repl) match {
      case Connect(_, EmptyExpression, _) => EmptyStmt
      case s => s
    }
    
  def inferReadWrite(m: DefModule) = {
    val connects = getConnects(m)
    val repl = new Connects
    val stmts = new Statements
    (m map inferReadWriteStmt(connects, repl, stmts)
       map replaceStmt(repl)) match {
      case m: ExtModule => m
      case m: Module => m copy (body = Block(m.body +: stmts))
    }
  }

  def run(c: Circuit) = c copy (modules = (c.modules map inferReadWrite))
}

// Transform input: Middle Firrtl. Called after "HighFirrtlToMidleFirrtl"
// To use this transform, circuit name should be annotated with its TransId.
class InferReadWrite(transID: TransID) extends Transform with LazyLogging {
  def execute(circuit:Circuit, map: AnnotationMap) = map get transID match {
    case Some(p) => p get CircuitName(circuit.main) match {
      case Some(InferReadWriteAnnotation(_, _)) => TransformResult((Seq(
        InferReadWritePass,
        CheckInitialization,
        ResolveKinds,
        InferTypes,
        ResolveGenders) foldLeft circuit){ (c, pass) =>
          val x = Utils.time(pass.name)(pass run c)
          logger debug x.serialize
          x
        }, None, Some(map))
      case _ => TransformResult(circuit, None, Some(map))
    }
    case _ => TransformResult(circuit, None, Some(map))
  }
}
