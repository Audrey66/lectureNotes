// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(list.size > 0),
        Ensures(
            //nothing in seq is changing, need to describe return
            //whatever is returning is <= every element in seq
            ∀(0 until list.size)(k => Res[Z] <= list(k)),
            //whatever is returning is one of the elements
            ∃(0 until list.size)(k => Res[Z] == list(k))
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),
            //bound loop invar
            i >= 1, i <= list.size,
            //dont need change size cause doesnt change list

            //small is smallest looked at so far
            ∀(0 until i)(k => small <= list(k)),

            //small is one of the elements looked at so far
            ∃(0 until i)(k => small == list(k))
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)