// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? 
//no, need one before you lose information


x = x + 1

Deduce(
    1 ( Old(x) > 0 ) by Premise, //x was 0, just changed
    2 ( x == Old(x) + 1) by Premise,
    3 ( orig == Old(x)) by Premise,
    4 ( x == orig + 1) by Subst_>(3,2)

    //want x > 1
    //5 ( x > 1) by Algebra*(1,2)

)



x = x + 2

Deduce(
    1 ( x == Old(x) + 2) by Premise,
    2 (  Old(x) == orig + 1) by Premise, //was true in old block, but x has changes now
    3 ( x == orig + 1 + 2) by Subst_<(2,1),
    4 ( x == orig + 3) by Algebra*(3)
    //need x == orig + 3 (extra ex ^ x > 3)
    //need x > 3

    // 5 ( Old(x) > 1) by Premise, showed in previous block
    // 6 ( x > 3) by Algebra*(1,5),
    // 7 ( x == orig + 3 ^ x > 3) by AndI(4,6)
)


assert(x == orig + 3)//how would change if add ^ x > 3

