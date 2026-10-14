import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.CRT
import PrimeNumbers.Chapter2.Jacobi
import PrimeNumbers.Chapter2.SquareRoot
import PrimeNumbers.Chapter2.Hensel
import PrimeNumbers.Chapter2.Cornacchia
import PrimeNumbers.Chapter2.FiniteField
import PrimeNumbers.Chapter3.TrialDivision
import PrimeNumbers.Chapter3.ProbablePrime
import PrimeNumbers.Chapter4.NMinusOne
import PrimeNumbers.Chapter4.LucasLehmer
import PrimeNumbers.Chapter3.Sieve
import PrimeNumbers.Chapter9.IntSqrt
import PrimeNumbers.Chapter9.Multipoint
import PrimeNumbers.Chapter9.FastMul
import PrimeNumbers.Chapter9.Newton
import PrimeNumbers.Chapter9.FastMod
import PrimeNumbers.Chapter5.Fermat
import PrimeNumbers.Chapter5.Lehman
import PrimeNumbers.Chapter5.BabyGiant
import PrimeNumbers.Chapter5.PollardRho
import PrimeNumbers.Chapter5.PollardPMinusOne
import PrimeNumbers.Chapter5.RhoLog
import PrimeNumbers.Chapter5.PolyEval

/-!
# Running the algorithms

Sanity checks (`#guard` fails the build if a check is false) for the verified algorithms
of Chapter 2, including the worked examples from the book, and a few runs on large inputs
to show that the functions the theorems are about are the ones you would actually run.
-/

set_option linter.hashCommand false

namespace PrimeNumbers.Examples

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3 PrimeNumbers.Chapter4 PrimeNumbers.Chapter5

/-! ## §2.1.1 Euclid -/

#guard euclid 1071 462 = 21
#guard extEuclid 1071 462 = (-3, 7, 21)          -- (-3)·1071 + 7·462 = 21
#guard modInv 3 10 = 7                           -- the book's example before (2.4)
#guard euclidSteps 89 55 = 9                     -- consecutive Fibonacci numbers: worst case

/-! ## §2.1.2 Powers -/

#guard powMod 3 13 15 = 3                        -- the book's example `3^13 mod 15 = 3`
#guard pow (3 : ZMod 15) 13 = 3

/-! ## §2.1.3 CRT — the book's example `n ≡ 2, 2, 6 (mod 3, 5, 7)` gives `n = 62` -/

#guard crt ![3, 5, 7] ![2, 2, 6] = 62
#guard garner [3, 5, 7] [2, 2, 6] = 62

/-! ## §2.2 Polynomials

The book's example: `f = 7x¹¹ + x⁹ + 7x² + 1`, `g = -7x⁷ - x⁵ + 7x² + 1`.  Over `ℚ` the gcd
is `x² + 1/7`; over `F₁₃` it is `x² + 2`; over `F₇` it is `1`; over `F₂` it is
`x³ + x² + x + 1`.  Coefficient lists are written lowest degree first. -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `7x¹¹ + x⁹ + 7x² + 1` over any ring. -/
def exF (R : Type) [Ring R] : Chapter2.Poly R := [1, 0, 7, 0, 0, 0, 0, 0, 0, 1, 0, 7]

/-- `-7x⁷ - x⁵ + 7x² + 1` over any ring. -/
def exG (R : Type) [Ring R] : Chapter2.Poly R := [1, 0, 7, 0, 0, -1, 0, -7]

#guard Chapter2.Poly.gcd (exF ℚ) (exG ℚ) = [1 / 7, 0, 1]
#guard Chapter2.Poly.gcd (exF (ZMod 13)) (exG (ZMod 13)) = [2, 0, 1]
#guard Chapter2.Poly.gcd (exF (ZMod 7)) (exG (ZMod 7)) = [1]
#guard Chapter2.Poly.gcd (exF (ZMod 2)) (exG (ZMod 2)) = [1, 1, 1, 1]
#guard Chapter2.Poly.divMod ([0, 0, 1] : Chapter2.Poly ℚ) [2, 3] = ([-2 / 9, 1 / 3, 0], [4 / 9])
#guard (Chapter2.Poly.xgcd (exF (ZMod 13)) (exG (ZMod 13))).2.2 = [2, 0, 1]

-- The three irreducible quartics over `F₂` named in the book, and a reducible one.
#guard isIrreducible 2 [1, 1, 0, 0, 1]             -- x⁴ + x + 1
#guard isIrreducible 2 [1, 0, 0, 1, 1]             -- x⁴ + x³ + 1
#guard isIrreducible 2 [1, 1, 1, 1, 1]             -- x⁴ + x³ + x² + x + 1
#guard !isIrreducible 2 [1, 0, 1, 0, 1]            -- x⁴ + x² + 1 = (x² + x + 1)²
#guard isIrreducible 7 [1, 0, 1]                   -- x² + 1 over F₇ (the book's F₄₉)
#guard !isIrreducible 13 [1, 0, 1]                 -- x² + 1 = (x - 5)(x + 5) over F₁₃

/-! ## Operation counts -/

#guard powCost 1000000 = 25 ∧ 2 * Nat.log 2 1000000 = 38
#guard euclidSteps 832040 514229 = 28              -- F₃₀, F₂₉

/-! ## §2.3.1 Jacobi symbol — the book's example `(2/15) = 1` -/

#guard jacobi 2 15 = 1
#guard jacobi 1001 9907 = -1
#guard (List.range 13).map (fun a ↦ jacobi a 13) = [0, 1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1]

/-! ## §2.3.2 Square roots modulo `p`, in each of the cases of Algorithm 2.3.8 -/

/-- `x² ≡ a (mod p)` check on naturals. -/
def isSqrtMod (x a p : ℕ) : Bool := x * x % p = a % p

#guard isSqrtMod (sqrtMod 23 2).val 2 23         -- p ≡ 7 (mod 8)
#guard isSqrtMod (sqrtMod 19 5).val 5 19         -- p ≡ 3 (mod 8)
#guard isSqrtMod (sqrtMod 13 10).val 10 13       -- p ≡ 5 (mod 8)
#guard isSqrtMod (sqrtMod 41 21).val 21 41       -- p ≡ 1 (mod 8): Tonelli
#guard isSqrtMod (sqrtMod 257 2).val 2 257       -- p - 1 = 2^8: many loop passes
#guard findNonresidue 41 = 3
#guard jacobi (2 * 2 - 21) 41 = -1                -- so t = 2 works for a = 21 in Cipolla
#guard isSqrtMod (cipolla (21 : ZMod 41) 2).val 21 41
#guard findCipolla 41 21 = 2
#guard isSqrtMod (cipollaSqrt 41 21).val 21 41

/-! ## §2.3.3 Hensel lifting: `√2` in the 7-adic integers, starting from `3² ≡ 2 (mod 7)` -/

/-- `x² - 2`. -/
def sqMinusTwo : IntPoly := [-2, 0, 1]

#guard hensel sqMinusTwo 7 3 0 = (3, 7)
#guard hensel sqMinusTwo 7 3 1 = (10, 49)                   -- 10² = 100 = 2 + 2·49
#guard (hensel sqMinusTwo 7 3 3).1 ^ 2 % 7 ^ 8 = 2

/-! ## §2.3.4 Cornacchia–Smith -/

#guard cornacchia 13 1 = some (3, 2)             -- 13 = 3² + 2²
#guard cornacchia 103 2 = none                   -- (-2/103) = -1
#guard cornacchia 1009 1 = some (28, 15)         -- 1009 = 28² + 15²
#guard cornacchia 67 3 = some (8, 1)             -- 67 = 8² + 3·1²

/-! ## Large inputs

The Mersenne prime `p = 2^521 - 1` (157 digits).  The functions take `p` as an ordinary
argument, so `ZMod p` is never unfolded by the elaborator. -/

/-- A square root of `a` modulo `p` by Algorithm 2.3.8, as a natural number. -/
def sqrtModNat (a p : ℕ) : ℕ := (sqrtMod p (a : ZMod p)).val

/-- A square root of `a` modulo `p` by the general Tonelli branch with nonresidue `d`. -/
def tonelliNat (a d p : ℕ) : ℕ := (tonelli (a : ZMod p) (d : ZMod p)).val

/-- A square root of `a` modulo `p` by Algorithm 2.3.9 (Cipolla) with parameter `t`. -/
def cipollaNat (a t p : ℕ) : ℕ := (cipolla (a : ZMod p) (t : ZMod p)).val

/-- `2^521 - 1`, a Mersenne prime with `p ≡ 7 (mod 8)`. -/
def m521 : ℕ := 2 ^ 521 - 1

/-- `2^255 - 19`, a prime with `p ≡ 5 (mod 8)`. -/
def p25519 : ℕ := 2 ^ 255 - 19

/-- The NIST P-224 prime `2^224 - 2^96 + 1`, with `p - 1 = 2^96 · t`: the hard case for
Tonelli's algorithm (`s = 96`). -/
def p224 : ℕ := 2 ^ 224 - 2 ^ 96 + 1

set_option exponentiation.threshold 600 in
#guard powMod 3 (m521 - 1) m521 = 1                          -- Fermat
#guard jacobi 2 m521 = 1
#guard isSqrtMod (sqrtModNat 2 m521) 2 m521
#guard isSqrtMod (sqrtModNat 4 p25519) 4 p25519
#guard jacobi 2 p224 = 1
#guard jacobi (findNonresidue p224) p224 = -1
#guard isSqrtMod (sqrtModNat 2 p224) 2 p224                  -- Tonelli with s = 96
#guard isSqrtMod (tonelliNat 2 (findNonresidue m521) m521) 2 m521
#guard jacobi (1 * 1 - 2) m521 = -1                          -- so t = 1 works for a = 2
#guard isSqrtMod (cipollaNat 2 1 m521) 2 m521
#guard (extEuclid m521 p25519).2.2 = 1
#guard m521 * modInv m521 p25519 % p25519 = 1
#guard garner [m521, p25519, p224] [1, 2, 3] % p25519 = 2

/-! ## §3.1 Trial division (factoring) -/

#guard (trialDivision 360).reverse = [2, 2, 2, 3, 3, 5]
#guard (trialDivision 7399).reverse = [7, 7, 151]
#guard (trialDivision 1000001).reverse = [101, 9901]
#guard (trialDivision (2 ^ 32 + 1)).reverse = [641, 6700417]      -- Euler's factor of F₅
#guard isPrimeTD 1000003
#guard !isPrimeTD 1000001

/-! ## §3.4–3.5 Probable primes -/

#guard probablePrime 341 2                        -- 341 = 11·31 is a pseudoprime base 2 …
#guard !strongProbablePrime 341 2                 -- … but 2 is a witness for it
#guard strongProbablePrime 2047 2                 -- 2047 = 23·89, strong pseudoprime base 2
#guard !millerRabin 2047 [2, 3]
#guard probablePrime 561 2 && probablePrime 561 5 -- 561 = 3·11·17 is a Carmichael number
#guard !strongProbablePrime 561 2
#guard millerRabin m521 [2, 3, 5, 7, 11, 13]
#guard !millerRabin (m521 * p25519) [2]

/-! ## §4.1 Primality proofs from `n - 1` -/

#guard lucasTest 7 3
#guard lucasTest 65537 3
#guard (List.range 20).any (lucasTest 1009)       -- some small base is a primitive root
#guard !(List.range 30).any (lucasTest 1001)
#guard (List.range 6).map pepin = [false, true, true, true, true, false]   -- F₁ … F₄ prime
#guard !pepin 10                                  -- F₁₀ (309 digits) is composite

/-- The Proth prime `3 · 2^189 + 1` (58 digits): here `n - 1 = F R` with `F = 2^189`
fully factored and `F² ≥ n`, so one Pocklington check with `q = 2` proves primality. -/
def proth189 : ℕ := 3 * 2 ^ 189 + 1

#guard [5, 7, 11, 13].any fun a ↦ pocklingtonCheck proth189 a [2]

/-! ## §4.2 Lucas–Lehmer -/

#guard (List.range 32).filter lucasLehmer = [3, 5, 7, 13, 17, 19, 31]
#guard lucasLehmer 521
#guard lucasLehmer 2203
#guard !lucasLehmer 2207

/-! ## §5.2 Pollard rho -/

#guard pollardRho 8051 1 2 100 = some 97                       -- 8051 = 83 · 97
#guard pollardRho (2 ^ 32 + 1) 1 2 5000 = some 641             -- F₅ = 641 · 6700417
#guard pollardRho 97 1 2 1000 = none                           -- a prime: only the bad seed

/-- Cole's number `2^67 - 1 = 193707721 · 761838257287`. -/
def m67 : ℕ := 2 ^ 67 - 1

#guard pollardRho m67 1 2 200000 = some 193707721
#guard pollardRhoAcc m67 1 2 100 2000 = some 193707721          -- one gcd per 100 passes
#guard pollardBrent m67 1 2 400000 = some 193707721             -- Brent's cycle-finding
#guard pollardBrent 8051 1 2 100 = some 97

/-! ## §5.4 Pollard `p - 1` — the book's example `n = 2047 = 23 · 89` -/

#guard pollardPMinusOne 2047 10 = 1                -- B = 10: fails with g = 1
#guard pollardPMinusOne 2047 12 = 2047             -- B = 12: fails with g = n
#guard pollardPMinusOne 2047 8 12 = 89             -- start value c = 12, B = 8: success
#guard pm1Exponent 12 = 27720                      -- M(12) = lcm(1, …, 12)
#guard pollardPMinusOne 1403 5 = 61                -- 1403 = 23 · 61, and 60 ∣ M(5)

-- `p = 2^31 - 1` has `p - 1 = 2 · 3² · 7 · 11 · 31 · 151 · 331`, which is 331-powersmooth,
-- while `q = 2^61 - 1` has `1321 ∣ q - 1`.  With `c = 2` the method still fails with
-- `g = n = p q` (28 digits), because `2` has the small orders 31 and 61 modulo `p` and `q`
-- — the same phenomenon as for 2047.  With `c = 3` it finds `p`.
#guard pollardPMinusOne ((2 ^ 31 - 1) * (2 ^ 61 - 1)) 331 = (2 ^ 31 - 1) * (2 ^ 61 - 1)
#guard pollardPMinusOne ((2 ^ 31 - 1) * (2 ^ 61 - 1)) 331 3 = 2 ^ 31 - 1

/-! ## §3.2 Sieve of Eratosthenes -/

#guard sievePrimes 50 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
#guard (sievePrimes 100000).length = 9592                      -- π(10⁵)
#guard (sievePrimes 1000).all isPrimeTD

/-! ## §5.1.1 Fermat method -/

#guard fermat 8051 = some 83                       -- 8051 = 90² - 7² = 83 · 97
#guard fermat 1000001 = some 101
#guard fermat 97 = none                            -- so 97 is prime
#guard fermat 10007 = none

/-! ## §5.1.2 Lehman method -/

#guard (lehman 8051).map (8051 % ·) = some 0 ∧ lehman 8051 ≠ some 1
#guard (lehman 1000001).map (1000001 % ·) = some 0
#guard (lehman (1000003 * 1000033)).map (1000003 * 1000033 % ·) = some 0   -- two primes ≈ 10⁶
#guard lehman 1000003 = none                       -- a prime

/-! ## §5.3 Baby-steps, giant-steps: discrete logarithms modulo `p = 1000003` -/

#guard (bsgs 1000003 2 (powMod 2 123456 1000003) 1000003).map (powMod 2 · 1000003) =
  some (powMod 2 123456 1000003)
#guard (bsgs 101 2 3 100).map (powMod 2 · 101) = some 3      -- 2 is a primitive root of 101

/-! ## §9.2.2 Integer square root (Algorithm 9.2.11) -/

open PrimeNumbers.Chapter9 in
#guard (List.range 200).all fun N ↦ isqrt N = Nat.sqrt N
open PrimeNumbers.Chapter9 in
#guard isqrt (m521 * m521 + 12345) = m521
open PrimeNumbers.Chapter9 in
#guard isqrtSteps (m521 * m521) (2 ^ 521) ≤ 522

/-! ## §5.4 Second stage of `p - 1`

`4243 - 1 = 2 · 3 · 7 · 101`: stage one with `B = 10` misses the factor `101`, and the
second stage with `B' = 150` finds it. -/

#guard pollardPMinusOne (4243 * 1000003) 10 = 1
#guard pollardStage2 (4243 * 1000003) 10 150 = 4243
#guard stage2Primes 10 30 = [11, 13, 17, 19, 23, 29]

/-! ## §5.2.2 Rho for discrete logarithms, in subgroups of prime order -/

#guard rhoLog 1019 509 4 (powMod 4 123 1019) 1000 = some 123     -- `4` has order 509 mod 1019
#guard rhoLog 2039 1019 4 (powMod 4 777 2039) 5000 = some 777    -- order 1019 mod 2039

/-! ## §5.5 Polynomial evaluation method: always the least prime factor -/

#guard pollardStrassen 8051 = some 83
#guard pollardStrassen 1000001 = some 101
#guard pollardStrassen (1000003 * 1000033) = some 1000003
#guard pollardStrassen 1000003 = none              -- a prime
#guard pollardStrassenFast 8051 = some 83          -- with fast multipoint evaluation
#guard pollardStrassenFast (1000003 * 1000033) = some 1000003
#guard pollardStrassenFast 1000003 = none

/-! ## §9.6 Algorithm 9.6.7: evaluation at many points

Over `ℤ`, and over `Z_n` for the composite `n = 8051`, the recursive algorithm agrees with
direct evaluation at every point. -/

open PrimeNumbers.Chapter9 in
#guard multipointEval 2 ([3, -1, 4, 1, -5, 9] : Chapter2.Poly ℤ) [0, 1, 2, 3, 4, 5, 6, 7, 8] =
  [0, 1, 2, 3, 4, 5, 6, 7, 8].map (Poly.eval [3, -1, 4, 1, -5, 9])

open PrimeNumbers.Chapter9 in
#guard multipointEval 4 (prodLinear ((List.range 30).map ((↑) : ℕ → ZMod 8051)))
    ((List.range 30).map fun j ↦ ((30 * j : ℕ) : ZMod 8051)) =
  (List.range 30).map fun j ↦ Poly.eval (prodLinear ((List.range 30).map ((↑) : ℕ → ZMod 8051)))
    ((30 * j : ℕ) : ZMod 8051)

/-! ## §9.6.1 Binary segmentation agrees with schoolbook multiplication -/

open PrimeNumbers.Chapter9 in
#guard mulNatAuto [3, 1, 4, 1, 5, 9, 2, 6] [2, 7, 1, 8, 2, 8] =
  Chapter2.Poly.mul [3, 1, 4, 1, 5, 9, 2, 6] [2, 7, 1, 8, 2, 8]

open PrimeNumbers.Chapter9 in
#guard mulMod 8051 ((List.range 300).map ((↑) : ℕ → ZMod 8051))
    ((List.range 300).map fun i ↦ ((i * i + 7 : ℕ) : ZMod 8051)) =
  Chapter2.Poly.mul ((List.range 300).map ((↑) : ℕ → ZMod 8051))
    ((List.range 300).map fun i ↦ ((i * i + 7 : ℕ) : ZMod 8051))

/-! ## §9.6.2 Newton inversion modulo `t^64` in `Z_8051[t]` -/

open PrimeNumbers.Chapter9 in
#guard (mulMod 8051 ((List.range 100).map fun i ↦ ((i * i + 1 : ℕ) : ZMod 8051))
    (invNewton (mulMod 8051) ((List.range 100).map fun i ↦ ((i * i + 1 : ℕ) : ZMod 8051))
      1 6)).take 64 = 1 :: List.replicate 63 0

/-! ## §9.6.4 Fast remainder agrees with long division (as polynomials) -/

open PrimeNumbers.Chapter9 in
#guard Chapter2.Poly.trim (fastModMonic (mulMod 8051)
    ((List.range 200).map fun i ↦ ((i * i * i + 5 : ℕ) : ZMod 8051))
    (prodLinear ((List.range 40).map ((↑) : ℕ → ZMod 8051)))) =
  Chapter2.Poly.trim (Poly.modMonic ((List.range 200).map fun i ↦ ((i * i * i + 5 : ℕ) : ZMod 8051))
    (prodLinear ((List.range 40).map ((↑) : ℕ → ZMod 8051))))

end PrimeNumbers.Examples
