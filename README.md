# Prime Numbers: A Computational Perspective — in Lean 4

This is an attempt at a formalization of Crandall & Pomerance, *Prime
Numbers: A Computational Perspective* (2nd ed.), with the book's
algorithms written as ordinary, efficient Lean 4 functions and their
correctness theorems proved on those functions. The idea is to use as
much of Mathlib where it exists but otherwise to follow the structure
of the textbook.

I am trying to still figure out the right way to formalize the
algorithmic complexities of many of the results. One way is to use the
bit complexities in Chapter 9, but also to try and keep the abstract
operation counts so the cost models are more generic.

The initial part of this effort was generated with Claude Opus
5.5. This README will be updated as more parts of the book are
formalized. Most stuff outside of this section was only lightly
edited, so beware slop.

I thought this could also be a good foundation to do the exercises by
hand in Lean to learn the material better, but it may also be good to
try and use an LLM to solve and formalize the exercises. There have
also been significant advancements in some parts of the algorithm,
especially regarding deterministic factoring (Harvey & Hittmeir) and
with the pseudo-polynomial time algorithms for discrete logarithm that
may be worth formalizing as add-ons.

## Quickstart

You need [elan](https://github.com/leanprover/elan) (the Lean version manager); it
installs the right Lean version for this project automatically.

**Terminal**

```bash
lake exe cache get      # once: download prebuilt Mathlib (~5 min) instead of compiling it
lake build              # check every proof and run every `#guard` test
```

`lake build` prints `Build completed successfully` when all proofs check and all tests in
`PrimeNumbers/Examples.lean` pass.  To check or run a single file:

```bash
lake env lean PrimeNumbers/Chapter2/Euclid.lean
```

To try an algorithm yourself, put this in a scratch file `Scratch.lean` at the project
root and run `lake env lean Scratch.lean`:

```lean
import PrimeNumbers
open PrimeNumbers.Chapter2

#eval euclid 1071 462                       -- 21
#eval extEuclid 1071 462                    -- (-3, 7, 21)
#eval powMod 3 (2^127 - 2) (2^127 - 1)      -- 1
#eval jacobi 1001 9907                      -- -1
#eval garner [3, 5, 7] [2, 2, 6]            -- 62
#eval (sqrtMod 41 21).val                   -- a square root of 21 mod 41
#eval cornacchia 1009 1                     -- some (28, 15)
#eval isIrreducible 2 [1, 1, 0, 0, 1]       -- true: x⁴ + x + 1 over F₂

open PrimeNumbers.Chapter3 PrimeNumbers.Chapter4
#eval trialDivision 1000001                 -- [9901, 101]
#eval millerRabin (2^127 - 1) [2, 3, 5, 7]  -- true
#eval lucasLehmer 521                       -- true: 2^521 - 1 is prime
```

**VS Code**

1. Install the *Lean 4* extension (`leanprover.lean4`).
2. *File → Open Folder…* and choose this folder (the one containing `lakefile.toml`), not a
   single file.
3. Run `lake exe cache get` once in the integrated terminal.
4. Open any `.lean` file.  The *Lean Infoview* panel (`Ctrl/Cmd+Shift+Enter`) shows the
   proof state at the cursor and the output of `#eval`; errors are underlined in red.
   A file with no red underlines is fully checked.

## Conventions

* Declarations are named after the book: `theorem_2_1_6`, and each algorithm's docstring
  quotes the book's pseudocode.
* Where Mathlib already has a result, the book's statement is proved by citing Mathlib.
* Algorithms run on `ℕ`/`ℤ` (GMP-backed) or on `ZMod p`, which at run time is `Fin p`.
  Pass the modulus as a function argument (see `Examples.lean`) rather than writing
  `ZMod (2^521 - 1)` literally, which makes the elaborator unfold the number.

## Status

### Chapter 1 — `PrimeNumbers/Chapter1/Primes.lean`

| Book | Lean | Source |
|---|---|---|
| Thm 1.1.1 fundamental theorem of arithmetic | `theorem_1_1_1` | Mathlib |
| Thm 1.1.2 Euclid | `theorem_1_1_2` | Mathlib |
| Thm 1.1.3 Chebyshev | `theorem_1_1_3_upper`, `_lower` | Mathlib |
| Thm 1.1.5 Dirichlet | `theorem_1_1_5` | Mathlib |
| Thm 1.3.1 `2^q - 1` prime ⇒ `q` prime | `theorem_1_3_1` | Mathlib |
| Thm 1.3.2 Euler, factors of Mersenne numbers | `theorem_1_3_2` | proved here |
| Thm 1.3.3 Euclid–Euler, even perfect numbers | `theorem_1_3_3` | Mathlib Archive |
| Thm 1.3.4, 1.3.5 Fermat numbers | `theorem_1_3_4`, `theorem_1_3_5` | Mathlib |
| Thm 1.3.6 Wilson–Lagrange | `theorem_1_3_6` | Mathlib |
| Thm 1.4.1 Euler product; RH (statement) | `theorem_1_4_1`, `conjecture_1_4_1` | Mathlib |

Not formalized (not in Mathlib, stated without proof in the book): 1.1.4 (PNT), 1.2.1,
1.2.2, 1.4.2, 1.4.3, 1.4.5–1.4.7, 1.4.9.

### Chapter 2 — `PrimeNumbers/Chapter2/`

| Book | Lean function | Correctness theorem | File |
|---|---|---|---|
| Thm 2.1.1 | — | `theorem_2_1_1` | `Euclid` |
| Alg 2.1.2 Euclid | `euclid` | `euclid_eq_gcd` | `Euclid` |
| Thm 2.1.3 Lamé (worst case) | `euclidSteps` | `lame` | `Euclid` |
| Alg 2.1.4 extended Euclid | `extEuclid`, `modInv` | `extEuclid_spec`, `mul_modInv_modEq` | `Euclid` |
| Alg 2.1.5 powering | `pow`, `power`, `powMod` | `pow_eq`, `powMod_eq` | `Power` |
| (2.2), (2.3) | — | `euler_2_2`, `inverse_2_3` | `Power` |
| (2.4) polynomial arithmetic | `Poly.add`, `mul`, `divMod`, `mod` | `toPolynomial_mul`, `divMod_spec`, `toPolynomial_mod` | `Poly` |
| Alg 2.2.1 polynomial gcd | `Poly.gcd` | `toPolynomial_gcd` | `PolyGcd` |
| Alg 2.2.2 extended polynomial gcd | `Poly.xgcd` | `xgcd_spec` | `PolyGcd` |
| Thm 2.2.3, 2.2.5 (1,2,3,6), 2.2.7 | — | `theorem_2_2_3`, `theorem_2_2_5_*`, `theorem_2_2_7` | `FiniteField` |
| Thm 2.2.8 (1)⇔(2) | — | `theorem_2_2_8` | `FiniteField` |
| Alg 2.2.9 irreducibility test 1 | `isIrreducible`, `Poly.powMod` | `isIrreducible_iff` | `FiniteField` |
| Thm 2.1.6 CRT | `crt` | `theorem_2_1_6` | `CRT` |
| Alg 2.1.7 Garner | `Garner.precompute`, `Garner.reconstruct`, `garner` | `garner_spec` | `CRT` |
| Thm 2.3.4 (2.6)–(2.11) | — | `theorem_2_3_4_*` | `Jacobi` |
| Alg 2.3.5 Jacobi symbol | `jacobi` | `jacobi_eq` | `Jacobi` |
| Alg 2.3.8 Tonelli | `sqrtMod`, `tonelli`, `findNonresidue` | `sqrtMod_sq`, `tonelli_sq` | `SquareRoot` |
| Alg 2.3.9 Cipolla | `cipollaSqrt`, `cipolla`, `findCipolla` | `cipollaSqrt_sq`, `cipolla_sq` | `SquareRoot` |
| Alg 2.3.11 Hensel lifting | `hensel` | `hensel_spec` | `Hensel` |
| Alg 2.3.12 Cornacchia–Smith | `cornacchia` | `cornacchia_sound` (soundness only) | `Cornacchia` |

Running times are in the *Bit complexity* section below.

Open items in Chapter 2:

* Thm 2.2.8 (3) and **Alg 2.2.10**; Thm 2.2.5 (4), (5); formula (2.5).
* **Alg 2.3.10** (roots over `F_p`): the polynomial arithmetic it needs now exists.
* **Alg 2.3.12 completeness** (a representation is found whenever one exists) and
  **Alg 2.3.13**.
* Thm 2.1.3 average case.
* Thm 2.3.7 (Gauss sums).

### Running times — the cost models in `PrimeNumbers/Chapter9/BitCost.lean` and `Karatsuba.lean`

Running times are stated in **bit operations**, the book's measure, using the groundwork
of §9.1.  All future complexity analyses in this project use this layer.

* `Chapter9/BitCost.lean` defines a `CostModel`: the bit operations for one multiplication
  and one division-with-remainder as functions of the operands' bit lengths (the book's
  `M(n)`).  `school` is the grammar-school model of §9.1: `a·b` for a multiplication,
  `(a − b + 1)·b` for a division.
* For an algorithm `f`, `fCost C …` follows the recursion of `f` branch by branch and
  charges every multiplication and division `f` performs at the bit lengths of its actual
  operands.  Bounds are proved for an arbitrary cost model where that makes sense, then
  specialized to `school`.  Additions, comparisons and shifts (linear, and dominated by a
  neighbouring multiplication or division) are not charged.

With `k` the bit length of the modulus / input:

| Algorithm | Bit operations (grammar-school) | Theorem |
|---|---|---|
| 2.1.2 Euclid | ≤ `k(3k + 1)` — `O(ln² N)`, Exercise 2.6 | `euclidBitCost_school_le'` |
| 2.1.5 `xⁿ mod m` | ≤ `(4 log₂ n + 1)(k + 1)²` — `O(ln n · ln² m)`, Exercise 2.17 | `powModCost_school_le` (any model: `powModCost_le`) |
| 2.3.5 Jacobi symbol | ≤ `k(3k + 1)` — `O(ln² m)` | `jacobiBitCost_school_le'` |
| 2.1.4 extended Euclid, modular inverse | ≤ `4k(3k + 2)` and `4k(3k + 2) + k` — `O(ln² N)` | `extEuclidCost_school_le'`, `modInvCost_school_le` |
| 2.3.8 Tonelli (`p − 1 = 2^s t`) | ≤ `6 log₂ t + 4s² + 1` multiplications mod `p` — the book's `O(s² + ln t)`; ≤ `(6 log₂ t + 4s² + 1)(2k² + k)` bit operations | `tonelliMults_le`, `tonelliCost_school_le` |
| 2.3.8 full algorithm | ≤ `6 log₂ p + 4s² + 2` multiplications mod `p` (nonresidue search not counted) | `sqrtModMults_le` |
| 3.1.1 trial division | ≤ `(2 log₂ n + √n/2 + 1)·k(k + 1)` — `O(√n ln² n)` | `trialDivisionCost_school_le` (any model: `trialDivisionCost_le`) |
| 3.4.3 Fermat test | ≤ `(4 log₂ n + 1)(k + 1)²` — `O(ln³ n)` | `probablePrimeCost_school_le` |
| 3.5.2 strong probable prime test | ≤ `(4 log₂ n + 1)(k + 1)²` — `O(ln³ n)` per base | `strongProbablePrimeCost_school_le` (any model: `strongProbablePrimeCost_le`) |
| 4.1.2 Pepin test | ≤ `(4 log₂ F + 1)(k + 1)²` | `pepinCost_school_le` |
| 4.2.7 Lucas–Lehmer | ≤ `(p − 2)(2p² + p)` — `O(p³)` | `lucasLehmerCost_school_le` (any model: `lucasLehmerCost_le`) |
| §3.2 sieve of Eratosthenes | ≤ `N ln √N` bit writes unconditionally; ≤ `N (ln ln √N + c)` **assuming Mertens' theorem** (`Assumed.Mertens c`) | `sieveWrites_le_log`, `sieveWrites_le_of_mertens` |
| 9.2.11 integer square root | ≤ `⌈k/2⌉ + 1` Newton steps; ≤ `((k+1)/2 + 2)(k+1)²` bit operations | `isqrt_eq` (correctness), `isqrtSteps_le`, `isqrtCost_school_le` |
| 5.1.1 Fermat method | ≤ `(n+9)/6 + 1 − ⌈√n⌉` passes, each 2 multiplications + 1 integer square root; grammar-school with Algorithm 9.2.11: `O(n ln³ n)` | `fermatCost_le'`, `fermatCost_school_le` |
| 5.3.1 baby-steps giant-steps | ≤ `2b + 2 log₂ b` modular multiplications, `b = ⌊√n⌋ + 1`, + 1 modular inverse; grammar-school: `O(√n ln² p)` with explicit constants | `bsgsCost_le`, `bsgsCost_school_le` |

**A second cost model.**  `Chapter9/Karatsuba.lean` implements Karatsuba multiplication
(§9.5.1), proves it correct (`karatsuba_eq`) and proves its cost is `O(N^(log₂ 3))`
(`karatsubaCost_le`); `karatsubaModel` packages that as a `CostModel`, so every theorem
stated for an arbitrary cost model also holds with Karatsuba multiplication.  Its division
is still grammar-school.

**Where things are.**  `Chapter9/BitCost.lean` contains only the cost model and imports
nothing else from the project.  Each algorithm's file imports it and ends with a section
*Running time* holding, next to the correctness theorems: the plain operation count
(e.g. `euclidSteps_le`, `powCost_le`, `jacobiSteps_le`, `two_mul_trialSteps_le`,
`tonelliMults_le`), the bit-cost function `fCost`, its bound for an arbitrary cost model,
and the grammar-school corollary.

No bit-complexity bound yet for: extended Euclid's coefficient updates (2.1.4), Garner
(2.1.7), the polynomial algorithms (2.2.x), Cipolla (2.3.9), Hensel
(2.3.11), Cornacchia (2.3.12), and the Lucas/Pocklington certificate checkers (which also
depend on the cost of factoring `n − 1`).  The Tonelli bound counts multiplications
modulo `p` (each at most `C.mulMod k` bit operations) rather than summing bit costs.
Faster multiplication (§9.5) would be added as
further `CostModel`s.

### Chapter 3 — `PrimeNumbers/Chapter3/`

| Book | Lean function | Correctness theorem | File |
|---|---|---|---|
| Alg 3.1.1 trial division (factoring) | `trialDivision`, `isPrimeTD` | `trialDivision_spec`, `trialDivision_perm`, `isPrimeTD_iff` | `TrialDivision` |
| §3.2.1 sieve of Eratosthenes (basic form) | `sieve`, `sievePrimes` | `sieve_spec`, `mem_sievePrimes` | `Sieve` |
| Thm 3.4.1 Fermat's little theorem | — | `theorem_3_4_1` | `ProbablePrime` |
| Alg 3.4.3 probable prime test | `probablePrime` | `probablePrime_iff`, `probablePrime_of_prime` | `ProbablePrime` |
| Thm 3.4.4, 3.4.6 (Korselt) | — | `theorem_3_4_4`, `theorem_3_4_6` (Mathlib) | `ProbablePrime` |
| Thm 3.5.1 | — | `theorem_3_5_1` | `ProbablePrime` |
| Alg 3.5.2 strong probable prime test | `strongProbablePrime`, `millerRabin` | `strongProbablePrime_iff`, `strongProbablePrime_of_prime`, `not_prime_of_millerRabin` | `ProbablePrime` |

Open in Chapter 3: the blocked and wheel layouts of the sieve (Alg 3.2.1, 3.2.2 — the
sieve formalized is the plain array version they refine) and the smoothness test (3.3.1); the counting
theorems (3.4.2, 3.4.7, 3.5.4 "3/4 of bases are witnesses", 3.5.10–3.5.12) and the Miller
test 3.5.13 that depends on ERH; Lucas pseudoprimes (§3.6); prime counting (§3.7).
`theorem_3_4_6` uses Mathlib's definition of Carmichael number (`a^(n-1) ≡ 1` for `a`
coprime to `n`) rather than the book's (`a^n ≡ a` for all `a`).

### Chapter 4 — `PrimeNumbers/Chapter4/`

| Book | Lean function | Correctness theorem | File |
|---|---|---|---|
| Thm 4.1.1 Lucas | `lucasTest`, `lucasCheck` | `theorem_4_1_1`, `prime_of_lucasTest` | `NMinusOne` |
| Thm 4.1.2 Pepin | `pepin` | `theorem_4_1_2`, `pepin_iff` | `NMinusOne` |
| Thm 4.1.3 Pocklington, Cor 4.1.4 | `pocklingtonCheck` | `theorem_4_1_3`, `corollary_4_1_4`, `prime_of_pocklingtonCheck` | `NMinusOne` |
| Thm 4.2.6, Alg 4.2.7 Lucas–Lehmer | `lucasLehmer` | `lucasLehmer_iff` (number theory from Mathlib) | `LucasLehmer` |

Open in Chapter 4: Thm 4.1.5, 4.1.6 and Alg 4.1.7; the general `n + 1` tests (4.2.2–4.2.5,
4.2.8–4.2.10) and Alg 4.2.11; the finite field test (§4.3), Gauss sums test (§4.4) and
AKS (§4.5).

### Chapter 5 — `PrimeNumbers/Chapter5/`

| Book | Lean function | Theorems | File |
|---|---|---|---|
| Alg 5.1.1 Fermat method | `fermat` | `fermat_sound` (a returned `d` is a nontrivial divisor, `n > 3`), `fermat_none_prime` (no answer ⇒ odd `n` is prime) | `Fermat` |
| Alg 5.1.2 Lehman method, Thm 5.1.3 | `lehman` (with `k` up to `⌊n^{1/3}⌋ + 1`, one further than printed) | `lehman_sound` (a returned `d` is a nontrivial divisor, `n ≥ 576`); `theorem_5_1_3_complete` (no answer ⇒ `n` prime, via Dirichlet's approximation theorem); `lehmanPasses_le_cuberoot` (≤ `4 n^{1/3} + 2` passes) | `Lehman` |
| §5.4 second stage of `p − 1` | `pollardStage2`, `stage2Primes` | `pollardStage2_dvd`; `dvd_pollardStage2`: a prime `p ∣ n` with `p − 1 ∣ Q·M(B)` for a prime `Q ∈ (B, B']` divides the result | `PollardPMinusOne` |
| §5.2.2 rho for discrete logarithms (in `Z_p^*`) | `rhoLog` | `rhoLog_sound`; `iterate_rhoLogStep_inv` (the walk keeps `x = g^a t^b`); `pow_rhoLogSolve` (at a collision with `gcd(b − B, N) = 1` the candidate is the logarithm); `exists_rhoLog_collision` (a collision within `p` steps); assembled: `rhoLog_isSome` (within `p` passes it returns a logarithm, provided `b − B` is invertible mod `N` at every collision); `rhoLogWalkCost_le` (3 modular multiplications per pass) | `RhoLog` |
| §5.5 polynomial evaluation method (Pollard–Strassen) | `pollardStrassenFast` (fast multipoint evaluation), `pollardStrassen` (block by block) | `pollardStrassenFast_eq_minFac`: for composite `n` it returns the least prime factor; `pollardStrassenFast_eq` (both versions agree) | `PolyEval` |
| Alg 5.3.1 baby-steps, giant-steps (in `Z_p^*`, hash table) | `bsgs` | `bsgs_sound`: a returned `l` has `g^l ≡ t (mod p)`; `bsgs_complete`: an answer is returned whenever `t ≡ g^l` for some `l ≤ n` | `BabyGiant` |
| §5.2.1 rho with Brent's cycle-finding | `pollardBrent` | `pollardBrent_sound`; `pollardBrentLoop_isSome_of_collision`: stops within `4T` steps given `RhoCollision p a s T` (so within `4p` unconditionally); `pollardBrentCost_le`: one modular multiplication + one gcd per step | `PollardRho` |
| §5.2.1 rho with accumulated gcd's | `pollardRhoAcc` | `pollardRhoAcc_sound`; `rhoBatchCost_le`: 4 modular multiplications per pass, one gcd per batch | `PollardRho` |
| Alg 5.2.1 Pollard rho | `pollardRho` (seeds `a`, `s` and a pass limit `fuel` supplied by the caller) | `pollardRho_sound`: any answer is a nontrivial factor; `pollardRhoLoop_isSome`: the search stops within `p` passes for any divisor `p > 1`, via Floyd cycle-finding `floyd`; **conditional on the heuristic**, `pollardRhoLoop_isSome_of_collision`: it stops within `T` passes if the sequence mod `p` repeats within `T` steps (`RhoCollision p a s T`) | `PollardRho` |
| Alg 5.4.1 Pollard `p − 1` | `pollardPMinusOne`, `pm1Exponent` (`M(B)`), `ladders` | `pollardPMinusOne_dvd`; `ladder_eq`: `c ≡ c₀^M(B)`; `dvd_pollardPMinusOne`, `pollardPMinusOne_ne_one`: a prime `p ∣ n` with `p − 1` `B`-powersmooth divides the result | `PollardPMinusOne` |

Bit complexity (in the same files), `k` the bit length of `n`:

| Algorithm | Bound | Theorem |
|---|---|---|
| 5.2.1 Pollard rho | per pass ≤ 3 modular multiplications + 1 gcd (any model); ≤ `9k² + 4k` grammar-school | `pollardRhoCost_le`, `pollardRhoCost_school_le` |
| 5.4.1 Pollard `p − 1` | ≤ `pm1Steps B` modular powers with exponents ≤ `B`, + 1 gcd (any model); `pm1Steps B ≤ π(B)·log₂ B` | `pm1Cost_le`, `pm1Cost_school_le`, `pm1Steps_le` |

**Heuristics as explicit hypotheses.**  The `O(√p)` running time of Pollard rho rests on
the unproved assumption that `x ↦ x² + a mod p` behaves like a random map.  That
assumption is stated as a definition, `RhoCollision p a s T` ("the sequence modulo `p`
repeats within `T` steps"; for a random map `T ≈ √(πp/2)` is expected), and the theorem is
proved *conditionally* on it: `RhoCollision p a s T` ⇒ at most `T` passes ⇒ at most
`T·(9k² + 4k)` bit operations.  Unconditionally `RhoCollision p a s p` holds
(`rhoCollision_self`), giving the rigorous `O(p ln² n)`.  A [Bad seed] (`g = n`) is
reported as `none`.

For `p − 1`, the result can be `n` itself even when the smoothness condition holds (see
the examples).  Its primes up to `B` now come from the sieve; the sieve's own cost is not
charged.

Further bit-cost bounds: Lehman's method, `lehmanCost_school_le` — at most
`(4 n^{1/3} + 2)(2K² + schoolSqrt (2K))` bit operations with `K ≈ (4/3) log₂ n`, i.e.
`O(n^{1/3} ln³ n)` (general model: `lehmanCost_le_passes`); second stage of `p − 1`,
`stage2Cost_school_le` — at most `(4 log₂ B' + 5)(k + 1)²` per prime `Q`; §5.5 with
block-by-block evaluation, `findBlockCost_le` — `B² ≈ √n` multiplications plus `B` gcds.

### §9.6 Polynomial arithmetic — `PrimeNumbers/Chapter9/Multipoint.lean` (started)

Over any commutative ring (so over `Z_n` for composite `n`):

| Book | Lean function | Theorem |
|---|---|---|
| division by a monic polynomial | `Poly.divModMonic`, `Poly.modMonic` | `divModMonic_spec`, `toPolynomial_modMonic` (Mathlib's `%ₘ`) |
| products `∏ (t − u)` | `prodLinear` | `lead_prodLinear`, `eval_prodLinear` |
| Alg 9.6.1 fast multiplication (binary segmentation), with GMP integer multiplication | `mulNat`, `mulNatAuto`, `mulMod` (in `Z_n[t]`), `pack`, `unpack` | `mulNat_eq` (= schoolbook product when coefficients fit), `coeff_mul_le`, `toPolynomial_mulMod`, `mulNatCost_le` (one `bD`-bit integer multiplication) |
| Alg 9.6.2 fast inversion (Newton iteration) | `invNewton` (any proved-correct multiplication `mulF`, e.g. `mulMod`) | `invNewton_spec`: `a h ≡ 1 (mod t^(2^k))` |
| Alg 9.6.4 fast remainder (via reversal and Newton inversion) | `fastModMonic` (any proved-correct `mulF`) | `toPolynomial_fastModMonic`: computes `%ₘ` (proof via Mathlib's `reflect_mul`) |
| Alg 9.6.7 running time | `multipointCost` | `multipointCost_le`: at most `(⌈log₂ D⌉ + 1) · S(D)` for any superadditive per-node bound `S` (the `log D` levels of the recursion); `length_fastModMonic_prodTree_le` discharges its length hypothesis for the fast routines |
| Alg 9.6.7 evaluation at arbitrary points | `multipointEval`; `multipointEvalWith` (any correct product/remainder routines); `multipointEvalFast` (over `Z_n` with `mulMod` and `fastModMonic`, product tree `prodTree`) | `multipointEval_eq`, `multipointEvalWith_eq`, `multipointEvalFast_eq` |

Still to do for §9.6: per-node bounds `S(d) = O(M(d) log d)` for the fast product tree and
fast remainder in terms of an abstract polynomial-multiplication cost `M`, to instantiate
`multipointCost_le` and obtain the `O(n^{1/4} ln² n)` bound for §5.5; a quasi-linear `M`
(Nussbaumer, Algorithm 9.5.25); using fast multiplication
and remainder inside Algorithm 9.6.7; evaluation on arithmetic and geometric
progressions (9.6.5, 9.6.6), and the running-time analysis `O(D ln² D)` with fast
multiplication; then plugging Algorithm 9.6.7 into §5.5.

Open in Chapter 5: Algorithm 9.6.7 (fast polynomial multiplication and multipoint
evaluation), which is what brings §5.5 down to `O(n^{1/4} ln² n)` operations — the current
bound for §5.5 is the `√n` of block-by-block evaluation; §5.6 (binary quadratic forms:
Algorithms 5.6.2, 5.6.3, 5.6.7 and Theorems 5.6.1, 5.6.4).

### Assumed theorems — `PrimeNumbers/Assumed.lean`

Deep results the book states without proof and Mathlib does not have are written as
*propositions*, never as axioms: `Assumed.Mertens c` (Theorem 1.4.2),
`Assumed.PrimeNumberTheorem` (1.1.4), `Assumed.Brun` (1.2.1).  A theorem that needs one
takes it as a hypothesis (so far only `sieveWrites_le_of_mertens`), so the dependence is
visible in its statement and `#print axioms` stays at the three standard axioms.
Algorithm-specific heuristics are handled the same way next to the algorithm
(`RhoCollision` for Pollard rho).

`PrimeNumbers/Examples.lean` runs every algorithm, on the book's worked examples and on
inputs of 58–157 digits.
