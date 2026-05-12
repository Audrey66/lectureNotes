// #Sireum #Logika

//∀ ∃

import org.sireum._

var balance: Z = 0
var elite: B = F
val eliteMin: Z = 1000000 // $1M is the minimum balance for elite members

//these are the global invariants
@spec def inv = Invariant(
  balance >= 0, // balance should never be negative
  elite == (balance >= eliteMin) // elite flag should correspond to whether or not over 100000
)

def deposit(amount: Z): Unit = {
    Contract(
        Requires(amount >= 0),
        Modifies(balance, elite),
        Ensures(
            //describe how global variable change
            balance == In(balance) + amount
            //global variables are unwritten postconditions, dont need again
        )
    )
    //unwritten precondition about the global invariants?
    //unwritten postcondition about the global invariants?

    balance = balance + amount

    if (balance >= eliteMin) {
        elite = true
    }
}

def withdraw(amount: Z): Unit = {
    Contract(
        //dont allow balance become negative
        Requires(
            amount <= balance,
            amount >= 0
        ),
        Modifies(balance, elite),
        Ensures(
            balance == In(balance) - amount
        )
    )
    //unwritten precondition about the global invariants?
    //unwritten postcondition about the global invariants?

    balance = balance - amount

    if (balance < eliteMin) {
        elite = false
    }
}

//////////////// Test code /////////////////////

deposit(500000)
assert(balance == 500000 & !elite)
deposit(600000)
assert(balance == 1100000 & elite)
withdraw(150000)
assert(balance == 950000 & !elite)
deposit(200000)
assert(balance == 1150000 & elite)