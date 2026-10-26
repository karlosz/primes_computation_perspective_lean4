import PrimeNumbers.Chapter5.McKee

/-!
# Theorem 5.6.4: the running time of McKee's test

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.6.2.

The book's running times of factoring methods count *operations with integers*: the
measure here is `stepCount`, the cost model in which every multiplication, division and step
of the code (a call, a list cell) counts one.  The primitives are bounded where they are
defined, for any cost model (`modInvCost_le`, `powModCost_le`, `tonelli_cost_le`,
`isqrtCost_le`, `trialDivisionCost_le`) or in operations (`rootsMod_ops_le`, Exercise 2.36);
this file adds up McKee's search.
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3 PrimeNumbers.Chapter9

end PrimeNumbers.Chapter5
