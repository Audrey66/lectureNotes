// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(
      y >= 0 // prevent infinite recursion
    ),
    Ensures(
      Res[Z] == x * y 
    )
  )


  var total: Z = 0
  var i: Z = 0

  //what goes here?
  // base case: prove invarients hold initially

//need: total == i*x

  Deduce(
    1 ( total == 0) by Premise,
    2 ( i == 0) by Premise,
    3 (total == i * x) by Algebra*(1,2) //proves invarient
  )

  while (i != y) {
    //what goes here?
    Invariant(
      Modifies(total, i),
      //summarized the progress so far, relates the values of variables to each other
      //often looks similar to teh postcondidtion
      //we are making a table showing what total and i is before loop, then for each iteration
      //find pattern of how they relate, total- 0,x,2x,3x; i-0,1,2,3 | total == i * x/ total == x * y
      total == i*x
    )

    Deduce(
      1 ( total == i*x) by Premise //this is like inductive hypothesis. assume invarient is true at beginning of iteration
    )

    total = total + x
    Deduce(//processing total change to not lose value
      1 ( total == Old(total) + x) by Premise,
      2 ( Old(total) == i*x) by Premise,
      3 ( total == (i*x) + x) by Subst_<(2,1) //Algebra*(1,2)
    )

    i = i + 1
    //need: total == i*x
    Deduce(
      1 ( total == Old(i) * x + x) by Premise,
      2 ( i == Old(i) + 1) by Premise,
      3 ( Old(i) == i - 1) by Algebra*(2),
      4 ( total == (i-1) * x + x) by Subst_<(3,1), //algebra*(1,3)
      5 ( total == i * x - x + x) by Algebra*(4),
      6 ( total == i*x) by Algebra*(5)
    )


    //what should we be able to assert here?
  }

  Deduce(
    1 ( total == i*x) by Premise,
    2 ( !(i != y)) by Premise, // loop condition is false
    3 ( i == y) by Algebra*(2),
    4 ( total == x*y) by Algebra*(1,3) // subst_>(1,3)
  )

  //what do we need here?
  //need total == x*y

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

//prove preconditon: b >= 0

Deduce(
  1 ( b == 4) by Premise,
  2 ( b >= 0) by Algebra*(1)
)

var ans: Z = mult(a, b)

Deduce(
  1 (ans == a * b) by Premise,
  2 ( a ==5 ) by Premise,
  3 ( b == 4) by Premise,
  4 ( ans == 20) by Algebra*(1,2,3)
)

//what do we want to assert that ans is?
assert(ans == 20)