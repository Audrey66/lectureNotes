// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ¬(∃ x P(x)) |- ∀ x ¬P(x)

@pure def bothQuant[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 ( !(∃((x: T) => P(x))) ) by Premise,
      //use AllI to prove ∀((x: T) => !P(x))
      2 Let((a:T) => Subproof(
        //use negI to prove goal of !P(a)
        3 SubProof(
          4 Assume(P(a)),
          //can contradict w premise if have ∃((x: T) => P(x))
          5 (∃((x: T) => P(x))) by ExistsI[T](4),
          6 ( F ) by NegE(5,1)
          //goal: F
        ),
        7 ( !P(a)) by NegI(3)
        //goal: !P(a)
      )),
      8 (∀((x: T) => !P(x))) by AllI[T](2)
      //goal: ∀((x: T) => !P(x))
    )
  )
}