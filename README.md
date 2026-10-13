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

### Bit complexity — `PrimeNumbers/Chapter9/`

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
| 2.3.8 Tonelli (`p − 1 = 2^s t`) | ≤ `6 log₂ t + 4s² + 1` multiplications mod `p` — the book's `O(s² + ln t)`; `O(ln⁴ p)` worst case, `O(ln³ p)` for small `s` | `tonelliMults_le` |
| 3.1.1 trial division | ≤ `(2 log₂ n + √n/2 + 1)·k(k + 1)` — `O(√n ln² n)` | `trialDivisionCost_school_le` (any model: `trialDivisionCost_le`) |
| 3.4.3 Fermat test | ≤ `(4 log₂ n + 1)(k + 1)²` — `O(ln³ n)` | `probablePrimeCost_school_le` |
| 3.5.2 strong probable prime test | ≤ `(4 log₂ n + 1)(k + 1)²` — `O(ln³ n)` per base | `strongProbablePrimeCost_school_le` (any model: `strongProbablePrimeCost_le`) |
| 4.1.2 Pepin test | ≤ `(4 log₂ F + 1)(k + 1)²` | `pepinCost_school_le` |
| 4.2.7 Lucas–Lehmer | ≤ `(p − 2)(2p² + p)` — `O(p³)` | `lucasLehmerCost_school_le` (any model: `lucasLehmerCost_le`) |

The step counts these rest on (Lamé's bound `euclidSteps_le`, `powCost_le`,
`jacobiSteps_le`, `two_mul_trialSteps_le`) are in `Chapter2/Complexity.lean` and
`Chapter3/TrialDivision.lean`.

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
| Thm 3.4.1 Fermat's little theorem | — | `theorem_3_4_1` | `ProbablePrime` |
| Alg 3.4.3 probable prime test | `probablePrime` | `probablePrime_iff`, `probablePrime_of_prime` | `ProbablePrime` |
| Thm 3.4.4, 3.4.6 (Korselt) | — | `theorem_3_4_4`, `theorem_3_4_6` (Mathlib) | `ProbablePrime` |
| Thm 3.5.1 | — | `theorem_3_5_1` | `ProbablePrime` |
| Alg 3.5.2 strong probable prime test | `strongProbablePrime`, `millerRabin` | `strongProbablePrime_iff`, `strongProbablePrime_of_prime`, `not_prime_of_millerRabin` | `ProbablePrime` |

Open in Chapter 3: the sieves (Alg 3.2.1, 3.2.2) and smoothness test (3.3.1); the counting
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

`PrimeNumbers/Examples.lean` runs every algorithm, on the book's worked examples and on
inputs of 58–157 digits.
