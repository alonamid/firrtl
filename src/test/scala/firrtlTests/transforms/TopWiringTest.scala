// See LICENSE for license details.

package firrtlTests
package transform

import org.scalatest.FlatSpec
import org.scalatest.Matchers
import org.scalatest.junit.JUnitRunner
import scala.io.Source
import java.io._

import firrtl._
import firrtl.ir.{Circuit, Type, GroundType, IntWidth}
import firrtl.Parser
import firrtl.passes.PassExceptions
import firrtl.annotations.{
   Named,
   CircuitName,
   ModuleName,
   ComponentName,
   Annotation
}
import firrtl.transform.TopWiring._


/**
 * Tests TopWiring transformation
 */
class TopWiringTests extends LowTransformSpec {

   def TopWiringDummyOutputFilesFunction(dir: String, mapping: Seq[((ComponentName, Type, Boolean, Seq[String], String), Int)], state: CircuitState): CircuitState = {
     state
   }

   def TopWiringTestOutputFilesFunction(dir: String, mapping: Seq[((ComponentName, Type, Boolean, Seq[String], String), Int)], state: CircuitState): CircuitState = {
     val testOutputFile = new PrintWriter(new File(dir, "TopWiringOutputTest.txt" ))
     mapping map {
          case ((_, tpe, _, path, prefix), index) => {
            val portwidth = tpe match { case GroundType(IntWidth(w)) => w }
            val portnum = index
            val portname = prefix + path.mkString("_")
            testOutputFile.append(s"new top level port $portnum : $portname, with width $portwidth \n")
          }
     }
     testOutputFile.close()
     state
   }

   def transform = new TopWiringTransform
   "The signal x in module C" should "be connected to Top port with topwiring prefix and outputfile in /tmp" in {
      val input =
         """circuit Top :
           |  module Top :
           |    inst a1 of A
           |    inst a2 of A_
           |  module A :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst b1 of B
           |  module A_ :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst c1 of C
           |  module C:
           |    output x: UInt<1>
           |    x <= UInt(0)
           """.stripMargin
      val topwiringannos = Seq(TopWiringAnnotation(ComponentName(s"x", ModuleName(s"C", CircuitName(s"Top"))), s"topwiring_"),
                         TopWiringOutputFilesAnnotation(s"/tmp", TopWiringTestOutputFilesFunction)) 
      val check =
         """circuit Top :
           |  module Top :
           |    output topwiring_a1_b1_c1_x: UInt<1>
           |    inst a1 of A
           |    inst a2 of A_
           |    topwiring_a1_b1_c1_x <= a1.topwiring_b1_c1_x
           |  module A :
           |    output x: UInt<1>
           |    output topwiring_b1_c1_x: UInt<1>
           |    inst b1 of B
           |    x <= UInt(1)
           |    topwiring_b1_c1_x <= b1.topwiring_c1_x
           |  module A_ :
	   |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    output topwiring_c1_x: UInt<1>
           |    inst c1 of C
           |    x <= UInt(1)
           |    topwiring_c1_x <= c1.topwiring_x
           |  module C:
           |    output x: UInt<1>
           |    output topwiring_x: UInt<1>
           |    x <= UInt(0)
           |    topwiring_x <= x
           """.stripMargin
      execute(input, check, topwiringannos)
   }

   "The signal x in module C inst c1 and c2" should "be connected to Top port with topwiring prefix and outfile in /tmp" in {
      val input =
         """circuit Top :
           |  module Top :
           |    inst a1 of A
           |    inst a2 of A_
           |  module A :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst b1 of B
           |  module A_ :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst c1 of C
           |    inst c2 of C
           |  module C:
           |    output x: UInt<1>
           |    x <= UInt(0)
           """.stripMargin
      val topwiringannos = Seq(TopWiringAnnotation(ComponentName(s"x", ModuleName(s"C", CircuitName(s"Top"))), s"topwiring_"),
                         TopWiringOutputFilesAnnotation(s"/tmp", TopWiringTestOutputFilesFunction))
      val check =
         """circuit Top :
           |  module Top :
           |    output topwiring_a1_b1_c1_x: UInt<1>
           |    output topwiring_a1_b1_c2_x: UInt<1>
           |    inst a1 of A
           |    inst a2 of A_
           |    topwiring_a1_b1_c1_x <= a1.topwiring_b1_c1_x
           |    topwiring_a1_b1_c2_x <= a1.topwiring_b1_c2_x
           |  module A :
           |    output x: UInt<1>
           |    output topwiring_b1_c1_x: UInt<1>
           |    output topwiring_b1_c2_x: UInt<1>
           |    inst b1 of B
           |    x <= UInt(1)
           |    topwiring_b1_c1_x <= b1.topwiring_c1_x
           |    topwiring_b1_c2_x <= b1.topwiring_c2_x
           |  module A_ :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    output topwiring_c1_x: UInt<1>
           |    output topwiring_c2_x: UInt<1>
           |    inst c1 of C
           |    inst c2 of C
           |    x <= UInt(1)
           |    topwiring_c1_x <= c1.topwiring_x
           |    topwiring_c2_x <= c2.topwiring_x
           |  module C:
           |    output x: UInt<1>
           |    output topwiring_x: UInt<1>
           |    x <= UInt(0)
           |    topwiring_x <= x
           """.stripMargin
      execute(input, check, topwiringannos)
   }

   "The signal x in module C" should "be connected to Top port with topwiring prefix and outputfile in /tmp, after name colission" in {
      val input =
         """circuit Top :
           |  module Top :
           |    inst a1 of A
           |    inst a2 of A_
           |    wire topwiring_a1_b1_c1_x : UInt<1>
           |    topwiring_a1_b1_c1_x <= UInt(0)
           |  module A :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst b1 of B
           |    wire topwiring_b1_c1_x : UInt<1>
           |    topwiring_b1_c1_x <= UInt(0)
           |  module A_ :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst c1 of C
           |  module C:
           |    output x: UInt<1>
           |    x <= UInt(0)
           """.stripMargin
      val topwiringannos = Seq(TopWiringAnnotation(ComponentName(s"x", ModuleName(s"C", CircuitName(s"Top"))), s"topwiring_"),
                         TopWiringOutputFilesAnnotation(s"/tmp", TopWiringTestOutputFilesFunction)) 
      val check =
         """circuit Top :
           |  module Top :
           |    output topwiring_a1_b1_c1_x_0: UInt<1>
           |    inst a1 of A
           |    inst a2 of A_
           |    node topwiring_a1_b1_c1_x = UInt<1>("h0")
           |    topwiring_a1_b1_c1_x_0 <= a1.topwiring_b1_c1_x_0
           |  module A :
           |    output x: UInt<1>
           |    output topwiring_b1_c1_x_0: UInt<1>
           |    inst b1 of B
           |    node topwiring_b1_c1_x = UInt<1>("h0")
           |    x <= UInt(1)
           |    topwiring_b1_c1_x_0 <= b1.topwiring_c1_x
           |  module A_ :
	   |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    output topwiring_c1_x: UInt<1>
           |    inst c1 of C
           |    x <= UInt(1)
           |    topwiring_c1_x <= c1.topwiring_x
           |  module C:
           |    output x: UInt<1>
           |    output topwiring_x: UInt<1>
           |    x <= UInt(0)
           |    topwiring_x <= x
           """.stripMargin
      execute(input, check, topwiringannos)
   }

   "The signal x in module C" should "be connected to Top port with topwiring prefix and no output function" in {
      val input =
         """circuit Top :
           |  module Top :
           |    inst a1 of A
           |    inst a2 of A_
           |  module A :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst b1 of B
           |  module A_ :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    x <= UInt(1)
           |    inst c1 of C
           |  module C:
           |    output x: UInt<1>
           |    x <= UInt(0)
           """.stripMargin
      val topwiringannos = Seq(TopWiringAnnotation(ComponentName(s"x", ModuleName(s"C", CircuitName(s"Top"))), s"topwiring_"))
      val check =
         """circuit Top :
           |  module Top :
           |    output topwiring_a1_b1_c1_x: UInt<1>
           |    inst a1 of A
           |    inst a2 of A_
           |    topwiring_a1_b1_c1_x <= a1.topwiring_b1_c1_x
           |  module A :
           |    output x: UInt<1>
           |    output topwiring_b1_c1_x: UInt<1>
           |    inst b1 of B
           |    x <= UInt(1)
           |    topwiring_b1_c1_x <= b1.topwiring_c1_x
           |  module A_ :
	   |    output x: UInt<1>
           |    x <= UInt(1)
           |  module B :
           |    output x: UInt<1>
           |    output topwiring_c1_x: UInt<1>
           |    inst c1 of C
           |    x <= UInt(1)
           |    topwiring_c1_x <= c1.topwiring_x
           |  module C:
           |    output x: UInt<1>
           |    output topwiring_x: UInt<1>
           |    x <= UInt(0)
           |    topwiring_x <= x
           """.stripMargin
      execute(input, check, topwiringannos)
   }
}
