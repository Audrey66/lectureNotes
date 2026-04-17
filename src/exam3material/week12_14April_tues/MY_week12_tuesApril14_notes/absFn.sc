// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    //no preconditions
    Ensures(
      Res[Z] >= 0
      Res[Z] == -1*numOrig | Res[Z] == numOrig
    )
  )

  var num: Z = numOrig

  //update num to be the absolute value of the input
  if (num < 0) {
    num = num * -1

  Deduce(
  1 ( Old(num) < 0)  by Premise,
  2 ( numOrig == Old(num)) by Premise,
  3 ( num == Old(num) * -1) by Premise,
  4 ( num >= 0 ) by Algebra*(1,3),
  5 ( num == -1 * numOrig) by Algebra*(2,3)
)
  } else {
    //do nothing -- num is already its own absolute value
    Deduce(
  1 ( !(num < 0)) by Premise,
  2 ( numOrig == num) by Premise,
  3 ( num >= 0) by Algebra*(1),
  4 ( num == numOrig) by Algebra*(2),
)
  }

  //what can we say here?
  //what do we need to prove by the end of the function?
Deduce(
  //need num >= 0, num == -1*numOrig | num == numOrig
  1 ( num >= 0 ) by Premise, // true in both paths
  2 ( num == -1*numOrig | num == numOrig) by Premise // LHS true in if, RHS true in else 
)

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?
val calc: Z = absVal(x)
// calc >= 0
//calc == -1*x |calc == x

//what should we be able to assert?
assert(calc == 4)