import PrimeNumbers

/-!
# Benchmark inputs

Deterministic pseudo-random numbers (splitmix64) and primes of a given bit length, found
with the verified Miller–Rabin test (Algorithm 3.5.2) on the first twelve prime bases,
which is deterministic below `3.3 · 10²⁴` and a probable-prime test beyond.
-/

namespace Bench

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3

/-- One step of splitmix64. -/
def splitmix (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- A pseudo-random number below `2^k`, determined by `seed`. -/
def randBelow2Pow (seed k : Nat) : Nat := Id.run do
  let mut x := 0
  let mut s := splitmix seed.toUInt64
  for _ in [0:(k + 63) / 64] do
    x := x * 2 ^ 64 + s.toNat
    s := splitmix s
  return x % 2 ^ k

/-- A pseudo-random number of exactly `k` bits (`k ≥ 1`). -/
def randBits (seed k : Nat) : Nat := 2 ^ (k - 1) + randBelow2Pow seed (k - 1)

/-- A pseudo-random number in `[0, n)`. -/
def randBelow (seed n : Nat) : Nat := randBelow2Pow seed (n.log2 + 64) % n

def isProbPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n < 1000 then isPrimeTD n
  else n % 2 == 1 && millerRabin n [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- The least probable prime `≥ n` satisfying `p`. -/
partial def nextPrimeWith (p : Nat → Bool) (n : Nat) : Nat :=
  if isProbPrime n && p n then n else nextPrimeWith p (n + 1)

def nextPrime (n : Nat) : Nat := nextPrimeWith (fun _ ↦ true) n

/-- A prime of (about) `k` bits. -/
def randPrime (seed k : Nat) : Nat := nextPrime (randBits seed k)

/-- A prime of about `k` bits with `p ≡ r (mod m)`. -/
def randPrimeMod (seed k m r : Nat) : Nat := nextPrimeWith (· % m == r) (randBits seed k)

/-- A prime `q` of about `k` bits such that `2q + 1` is prime too (a Sophie Germain prime). -/
def randSophieGermain (seed k : Nat) : Nat :=
  nextPrimeWith (fun q ↦ isProbPrime (2 * q + 1)) (randBits seed k)

/-- A product of two primes of `k / 2` bits each. -/
def semiprime (seed k : Nat) : Nat × Nat × Nat :=
  let p := randPrime seed (k / 2)
  let q := nextPrime (p + randBelow2Pow (seed + 1) (k / 2 - 1) + 2)
  (p * q, p, q)

/-- A pseudo-random list of `d` numbers below `n`. -/
def randList (seed d n : Nat) : List Nat :=
  (List.range d).map fun i ↦ randBelow (seed * 1000003 + i) n

end Bench
