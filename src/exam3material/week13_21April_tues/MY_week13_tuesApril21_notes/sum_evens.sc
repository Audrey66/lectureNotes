// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(n > 0),
    Ensures(Res[Z] == n*(n+1))
  )

  var sum: Z = 0
  var cur: Z = 0

  Deduce(//find all invariants, sum == cur*(cur+1)
    //sum == 0, cur == 0, n > 0(premise)
    //
  )


  while (cur != n) {
    //what about our loop invariant?
    Invarient(
      Modifies(cur, sum),
      sum == cur*(cur+1)
    )

    //list of premises:
    //sum == cur*(cur+1)
    //cur != n
    //n > 0
    //CANNOT LIST SUM==0,CUR==0 AS PREMISE, IDK WHAT LOOP WE BE ON

    //need to prove-
    //sum == cur*(cur+1)

    cur = cur + 1
    //need deduce to process how cur changed
    //learn something about cur change that doesnt use "Old"
    sum = sum + 2*cur
    //making a table to find how sum and cur are related

  }

   //list of premises:
   //!(cur != n)
   // sum == cur*(cur+1)
   //n > 0
   //cannot say sum == Old(sum) + 2*(cur)

  return sum
}

//////////// test code /////////

val num: Z = 5

//what premises?
//num == 5
//need to prove precondition
//num > 0

var sum5evens: Z = sumEvens(num)

//premises-
//sum5evens == num*(num+1)
//num == 5

//need to prove sum5evens == 30

//sum of first 5 evens: 2,4,6,8,10 
assert(sum5evens == 30)
