import Bench.Harness
import Bench.Inputs

/-!
# The benchmark cases, by problem

Each case runs the verified function itself (the one the correctness and cost theorems are
about), compiled.  `bound` is the proved bit-cost bound (in the grammar-school model unless
stated otherwise; the measured times use Lean's GMP-backed `Nat`, whose products are
subquadratic for large inputs) or, for heuristic algorithms, the expected count.
-/

namespace Bench

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter3 PrimeNumbers.Chapter4 PrimeNumbers.Chapter5
open PrimeNumbers.Chapter9 (isqrt karatsuba nussMul nussbaumer bitsOfPow2 mulMod invNewton fastModMonic prodTree
  multipointEval multipointEvalFast)

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- A 64-bit prime modulus for the polynomial benchmarks over `Z_n`. -/
def polyN : ℕ := 18446744073709551557

/-- A random polynomial over `Z_n` with `d` coefficients. -/
def randPoly (n seed d : ℕ) : PrimeNumbers.Chapter2.Poly (ZMod n) := (randList seed d n).map (↑)

def hashPoly {n : ℕ} (f : PrimeNumbers.Chapter2.Poly (ZMod n)) : UInt64 := hash (f.map ZMod.val)

/-- An action for a function of a polynomial over `Z_n`. -/
def polyTask {α : Type} {n : ℕ} (input : α) (f : α → PrimeNumbers.Chapter2.Poly (ZMod n)) : IO (IO UInt64) := do
  let r ← IO.mkRef input
  pure do pure (hashPoly (f (← r.get)))

/-! Lean stores naturals below `2^63` unboxed and larger ones as GMP numbers, at several
times the cost per operation.  The sizes of each exponential-time case stay on one side
of that boundary, or the fitted exponent mixes the two regimes. -/

def pow2s (a b : ℕ) : List ℕ := (List.range (b - a + 1)).map fun i ↦ 2 ^ (a + i)

def steps (a b d : ℕ) : List ℕ := (List.range ((b - a) / d + 1)).map (a + d * ·)

/-- `x² - 2`, for Hensel lifting. -/
def sqMinusTwo : IntPoly := [-2, 0, 1]

/-! ## Greatest common divisors and inverses -/

def gcdCases : List Case := [
  { problem := "gcd and inverses", name := "euclid", ref := "Alg 2.1.2"
    param := "bits of the inputs", bound := "k(3k+2)", growth := .poly 2
    sizes := pow2s 8 15
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k) fun (x, y) ↦ euclid x y },
  { problem := "gcd and inverses", name := "extEuclid", ref := "Alg 2.1.4"
    param := "bits of the inputs", bound := "O(k²)", growth := .poly 2
    sizes := pow2s 8 15
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k) fun (x, y) ↦ extEuclid x y },
  { problem := "gcd and inverses", name := "modInv", ref := "§2.1.1"
    param := "bits of the modulus", bound := "O(k²)", growth := .poly 2
    sizes := pow2s 8 15
    prepare := fun k ↦ task (randBits 1 (k - 1), randBits 2 k ||| 1) fun (x, m) ↦ modInv x m } ]

/-! ## Powers -/

def powerCases : List Case := [
  { problem := "modular powers", name := "powMod", ref := "Alg 2.1.5"
    param := "bits of base, exponent and modulus", bound := "2k mulMod(k) = O(k³)"
    growth := .poly 3, sizes := pow2s 6 12
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k, randBits 3 k) fun (x, e, m) ↦
      powMod x e m },
  { problem := "modular powers", name := "pow (in ZMod m)", ref := "Alg 2.1.5"
    param := "bits of base, exponent and modulus", bound := "O(k³)", growth := .poly 3
    sizes := pow2s 6 12
    prepare := fun k ↦ do
      let m := randBits 3 k
      task (randBits 1 k, randBits 2 k) fun (x, e) ↦ (pow (x : ZMod m) e).val } ]

/-! ## Chinese remainders -/

def crtCases : List Case := [
  { problem := "Chinese remainders", name := "garner", ref := "Alg 2.1.7"
    param := "number of 62-bit moduli", bound := "O(r²) word operations", growth := .poly 2
    sizes := pow2s 3 10
    prepare := fun r ↦ do
      let ms := (List.range r).map fun i ↦ randPrime (100 + i) 62
      task (ms, randList 7 r (2 ^ 61)) fun (ms, ns) ↦ garner ms ns },
  { problem := "Chinese remainders", name := "crt", ref := "Thm 2.1.6"
    param := "number of 62-bit moduli", bound := "O(r²) word operations", growth := .poly 2
    sizes := pow2s 3 9
    prepare := fun r ↦ do
      let ms := (List.range r).map fun i ↦ randPrime (100 + i) 62
      let ns := randList 7 r (2 ^ 61)
      task (ms, ns) fun (ms, ns) ↦
        crt (fun i : Fin ms.length ↦ ms[i]) (fun i : Fin ms.length ↦ ns.getD i 0) } ]

/-! ## Quadratic residues and square roots -/

def sqrtCases : List Case := [
  { problem := "quadratic residues and square roots", name := "jacobi", ref := "Alg 2.3.5"
    param := "bits of the inputs", bound := "O(k²)", growth := .poly 2
    sizes := pow2s 8 15
    prepare := fun k ↦ task ((randBits 1 k : ℤ), randBits 2 k ||| 1) fun (a, m) ↦ jacobi a m },
  { problem := "quadratic residues and square roots", name := "sqrtMod", ref := "Alg 2.3.8"
    param := "bits of the prime p", bound := "O(k³) (+ O(s² k²) for p - 1 = 2^s t)"
    growth := .poly 3, sizes := pow2s 6 11
    prepare := fun k ↦ do
      let p := randPrime 1 k
      let x := randBelow 2 p
      task (x * x % p) fun a ↦ (sqrtMod p (a : ZMod p)).val },
  { problem := "quadratic residues and square roots", name := "cipollaSqrt", ref := "Alg 2.3.9"
    param := "bits of the prime p", bound := "O(k³)", growth := .poly 3
    sizes := pow2s 6 11
    prepare := fun k ↦ do
      let p := randPrime 1 k
      let x := randBelow 2 p
      task (x * x % p) fun a ↦ (cipollaSqrt p (a : ZMod p)).val },
  { problem := "quadratic residues and square roots", name := "hensel", ref := "Alg 2.3.11"
    param := "2^i, the bits of the modulus 7^(2^i) over log₂ 7", bound := "O(K²) for the last step"
    growth := .poly 2, sizes := pow2s 6 13
    prepare := fun s ↦ task s.log2 fun i ↦ hensel sqMinusTwo 7 3 i },
  { problem := "quadratic residues and square roots", name := "cornacchia", ref := "Alg 2.3.12"
    param := "bits of the prime p ≡ 1 (mod 4)", bound := "O(k³) (the square root)"
    growth := .poly 3, sizes := pow2s 6 11
    prepare := fun k ↦ task (randPrimeMod 1 k 4 1) fun p ↦ cornacchia p 1 } ]

/-! ## Integer square roots -/

def isqrtCases : List Case := [
  { problem := "integer square roots", name := "isqrt", ref := "Alg 9.2.11"
    param := "bits of N", bound := "O(log k) divisions, O(k² log k)", growth := .poly 2
    sizes := pow2s 8 15
    prepare := fun k ↦ task (randBits 1 k) isqrt } ]

/-! ## Integer multiplication -/

def mulCases : List Case := [
  { problem := "integer multiplication", name := "Nat.mul (GMP, reference)", ref := "§9.5"
    param := "bits of the factors", bound := "(GMP)", growth := .poly 1
    sizes := pow2s 10 20
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k) fun (x, y) ↦ x * y },
  { problem := "integer multiplication", name := "karatsuba", ref := "Alg 9.5.1"
    param := "bits of the factors (2^j)", bound := "O(k^1.585)", growth := .poly 1.585
    sizes := pow2s 6 12
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k) fun (x, y) ↦ karatsuba k.log2 x y },
  { problem := "integer multiplication", name := "nussMul", ref := "Alg 9.5.25"
    param := "bits of the factors", bound := "292 k (log₂ k + 3)⁴ (bitModel)", growth := .poly 1
    sizes := pow2s 8 15
    prepare := fun k ↦ task (randBits 1 k, randBits 2 k) fun (x, y) ↦ nussMul x y },
  { problem := "integer multiplication", name := "nussbaumer (negacyclic, bits)"
    ref := "Alg 9.5.25", param := "length 2^k", bound := "2^k (2k² + 1) · 8 (2k + 2)² (bitModel)"
    growth := .poly 1, sizes := pow2s 8 17
    prepare := fun m ↦ task (bitsOfPow2 m.log2 (randBits 1 m), bitsOfPow2 m.log2 (randBits 2 m))
      fun (a, b) ↦ nussbaumer m.log2 a b } ]

/-! ## Polynomials over finite fields -/

def polyFieldCases : List Case := [
  { problem := "polynomials over finite fields", name := "Poly.gcd (over F_65537)"
    ref := "Alg 2.2.1", param := "degree", bound := "O(d²) field operations", growth := .poly 2
    sizes := pow2s 5 10
    prepare := fun d ↦ polyTask (randPoly 65537 1 (d + 1), randPoly 65537 2 d)
      fun (f, g) ↦ PrimeNumbers.Chapter2.Poly.gcd f g },
  { problem := "polynomials over finite fields", name := "isIrreducible (over F_2)"
    ref := "Alg 2.2.9", param := "degree", bound := "O(d³) field operations", growth := .poly 3
    sizes := pow2s 4 8
    prepare := fun d ↦ task ((randPoly 2 1 d) ++ [1]) fun f ↦ isIrreducible 2 f } ]

/-! ## Polynomial multiplication and division over `Z_n` -/

def polyMulCases : List Case := [
  { problem := "polynomial arithmetic over Z_n", name := "Poly.mul (schoolbook)", ref := "§9.6"
    param := "number of coefficients (64-bit n)", bound := "d² mulMod", growth := .poly 2
    sizes := pow2s 5 10
    prepare := fun d ↦ polyTask (randPoly polyN 1 d, randPoly polyN 2 d)
      fun (f, g) ↦ PrimeNumbers.Chapter2.Poly.mul f g },
  { problem := "polynomial arithmetic over Z_n", name := "mulMod (binary segmentation)"
    ref := "Alg 9.6.1", param := "number of coefficients (64-bit n)"
    bound := "one (d log n)-bit product + O(d) small ones", growth := .poly 1
    sizes := pow2s 5 13
    prepare := fun d ↦ polyTask (randPoly polyN 1 d, randPoly polyN 2 d)
      fun (f, g) ↦ mulMod polyN f g },
  { problem := "polynomial arithmetic over Z_n", name := "invNewton (with mulMod)"
    ref := "Alg 9.6.2", param := "precision 2^k", bound := "O(M(2^k))", growth := .poly 1
    sizes := pow2s 6 12
    prepare := fun d ↦ polyTask (1 :: randPoly polyN 1 (d - 1))
      fun a ↦ invNewton (mulMod polyN) a 1 d.log2 },
  { problem := "polynomial arithmetic over Z_n", name := "Poly.modMonic (long division)"
    ref := "§9.6", param := "degree d of the divisor (dividend 2d)", bound := "O(d²) mulMod"
    growth := .poly 2, sizes := pow2s 5 10
    prepare := fun d ↦ polyTask (randPoly polyN 1 (2 * d), randPoly polyN 2 d ++ [1])
      fun (f, g) ↦ PrimeNumbers.Chapter9.Poly.modMonic f g },
  { problem := "polynomial arithmetic over Z_n", name := "fastModMonic (with mulMod)"
    ref := "Alg 9.6.4", param := "degree d of the divisor (dividend 2d)", bound := "O(M(d))"
    growth := .poly 1, sizes := pow2s 5 12
    prepare := fun d ↦ polyTask (randPoly polyN 1 (2 * d), randPoly polyN 2 d ++ [1])
      fun (f, g) ↦ fastModMonic (mulMod polyN) f g } ]

/-! ## Evaluation at many points -/

def multipointCases : List Case := [
  { problem := "multipoint evaluation", name := "Horner at each point", ref := "§9.6.3"
    param := "degree = number of points", bound := "D² mulMod", growth := .poly 2
    sizes := pow2s 5 11
    prepare := fun d ↦ polyTask (randPoly polyN 1 d, randPoly polyN 2 d)
      fun (f, T) ↦ T.map (PrimeNumbers.Chapter9.Poly.eval f) },
  { problem := "multipoint evaluation", name := "multipointEval (schoolbook products)"
    ref := "Alg 9.6.7", param := "degree = number of points", bound := "O(D² log D) mulMod"
    growth := .poly 2, sizes := pow2s 5 10
    prepare := fun d ↦ polyTask (randPoly polyN 1 d, randPoly polyN 2 d)
      fun (f, T) ↦ multipointEval 4 f T },
  { problem := "multipoint evaluation", name := "multipointEvalFast", ref := "Alg 9.6.7"
    param := "degree = number of points", bound := "(log D + 1) nodeBound(D) = Õ(D)"
    growth := .poly 1, sizes := pow2s 5 12
    prepare := fun d ↦ polyTask (randPoly polyN 1 d, randPoly polyN 2 d)
      fun (f, T) ↦ multipointEvalFast polyN 4 f T } ]

/-! ## Sieving -/

def sieveCases : List Case := [
  { problem := "sieving", name := "sievePrimes", ref := "§3.2.1"
    param := "N", bound := "O(N log log N) writes", growth := .poly 1
    sizes := pow2s 14 22
    prepare := fun N ↦ task N fun N ↦ (sievePrimes N).length } ]

/-! ## Primality -/

/-- A Proth prime `c 2^m + 1` of about `k` bits. -/
def prothPrime (k : ℕ) : ℕ :=
  let m := k - 8
  let c := ((List.range 100000).find? fun c ↦ c % 2 == 1 && isProbPrime ((128 + c) * 2 ^ m + 1)).getD 0
  (128 + c) * 2 ^ m + 1

def primalityCases : List Case := [
  { problem := "primality", name := "isPrimeTD (trial division)", ref := "Alg 3.1.1"
    param := "bits of the prime", bound := "√n divisions", growth := .exp 0.5
    sizes := steps 20 44 4
    prepare := fun k ↦ task (randPrime 1 k) isPrimeTD },
  { problem := "primality", name := "millerRabin (4 bases)", ref := "Alg 3.5.6"
    param := "bits of the prime", bound := "4 powMod = O(k³)", growth := .poly 3
    sizes := pow2s 6 12
    prepare := fun k ↦ task (randPrime 1 k) fun n ↦ millerRabin n [2, 3, 5, 7] },
  { problem := "primality", name := "pocklingtonCheck (Proth primes)", ref := "Thm 4.1.3"
    param := "bits of n = c·2^m + 1", bound := "2 powMod = O(k³)", growth := .poly 3
    sizes := pow2s 6 12
    prepare := fun k ↦ do
      let n := prothPrime k
      let a := ((List.range 1000).find? fun a ↦ powMod (a + 2) ((n - 1) / 2) n == n - 1).getD 0 + 2
      task n fun n ↦ pocklingtonCheck n a [2] },
  { problem := "primality", name := "lucasLehmer", ref := "Alg 4.2.7"
    param := "exponent p of 2^p - 1", bound := "p squarings mod 2^p - 1 = O(p³)"
    growth := .poly 3, sizes := pow2s 7 13
    prepare := fun p ↦ task (nextPrime p) lucasLehmer },
  { problem := "primality", name := "pepin", ref := "Thm 4.1.2"
    param := "2^k, the bits of F_k", bound := "2^k squarings = O(4^k·2^k)", growth := .poly 3
    sizes := pow2s 6 12
    prepare := fun s ↦ task s.log2 pepin } ]

/-! ## Factoring -/

/-- Four semiprimes of `k` bits with balanced factors. -/
def semiprimes (k : ℕ) : List ℕ := (List.range 4).map fun i ↦ (semiprime (10 * k + i) k).1

/-- Four semiprimes `p q` of `k` bits with `q ≈ 2p` (the hard case for Fermat's method). -/
def fermatSemiprimes (k : ℕ) : List ℕ := (List.range 4).map fun i ↦
  let p := randPrime (10 * k + i) ((k - 1) / 2)
  p * nextPrime (2 * p)

def factoringCases : List Case := [
  { problem := "factoring", name := "trialDivision", ref := "Alg 3.1.1"
    param := "bits of n = pq (balanced)", bound := "√n divisions", growth := .exp 0.5
    sizes := steps 20 44 4
    prepare := fun k ↦ task (semiprimes k) fun ns ↦ ns.map trialDivision },
  { problem := "factoring", name := "fermat", ref := "Alg 5.1.1"
    param := "bits of n = pq, q ≈ 2p", bound := "O(√n) steps", growth := .exp 0.5
    sizes := steps 20 44 4
    prepare := fun k ↦ task (fermatSemiprimes k) fun ns ↦ ns.map fermat },
  { problem := "factoring", name := "lehman", ref := "Alg 5.1.2"
    param := "bits of n = pq (balanced)", bound := "(4n^{1/3} + 2) passes, O(n^{1/3} ln³ n)"
    growth := .exp (1 / 3), sizes := steps 20 44 4
    prepare := fun k ↦ task (semiprimes k) fun ns ↦ ns.map lehman },
  { problem := "factoring", name := "pollardRho", ref := "Alg 5.2.1"
    param := "bits of n = pq (balanced)", bound := "T passes, T ≈ √p (heuristic)"
    growth := .exp 0.25, sizes := steps 40 80 8
    prepare := fun k ↦ task (semiprimes k) fun ns ↦
      ns.map fun n ↦ pollardRho n 1 2 (2 ^ (k / 4 + 10)) },
  { problem := "factoring", name := "pollardBrent", ref := "§5.2.1"
    param := "bits of n = pq (balanced)", bound := "4T steps, T ≈ √p (heuristic)"
    growth := .exp 0.25, sizes := steps 40 80 8
    prepare := fun k ↦ task (semiprimes k) fun ns ↦
      ns.map fun n ↦ pollardBrent n 1 2 (2 ^ (k / 4 + 10)) },
  { problem := "factoring", name := "pollardRhoAcc", ref := "§5.2.1"
    param := "bits of n = pq (balanced)", bound := "T passes, a gcd per 100 (heuristic)"
    growth := .exp 0.25, sizes := steps 40 80 8
    prepare := fun k ↦ task (semiprimes k) fun ns ↦
      ns.map fun n ↦ pollardRhoAcc n 1 2 100 (2 ^ (k / 4 + 10)) },
  { problem := "factoring", name := "pollardStrassen (block by block)", ref := "§5.5"
    param := "bits of n = pq (balanced)", bound := "B² ≈ √n products", growth := .exp 0.5
    sizes := steps 20 40 4
    prepare := fun k ↦ task (semiprimes k) fun ns ↦ ns.map pollardStrassen },
  { problem := "factoring", name := "pollardStrassenFast", ref := "§5.5, Thm 5.5.3"
    param := "bits of n = pq (balanced)", bound := "2^35 n^{1/4} (log₂ n + 3)⁷ (nussModel)"
    growth := .exp 0.25, sizes := steps 24 56 4
    prepare := fun k ↦ task (semiprimes k) fun ns ↦ ns.map pollardStrassenFast },
  { problem := "factoring", name := "pollardPMinusOne", ref := "Alg 5.4.1"
    param := "smoothness bound B (128-bit n, no B-smooth p - 1)"
    bound := "π(B) log B modular products", growth := .poly 1, sizes := pow2s 10 17
    prepare := fun B ↦ task (semiprime 5 128).1 fun n ↦ pollardPMinusOne n B },
  { problem := "factoring", name := "pollardStage2", ref := "§5.4"
    param := "second bound B' (B = 1000, 128-bit n)", bound := "O(π(B') log B') products"
    growth := .poly 1, sizes := pow2s 12 18
    prepare := fun B' ↦ task (semiprime 5 128).1 fun n ↦ pollardStage2 n 1000 B' } ]

/-! ## Discrete logarithms -/

def dlogCases : List Case := [
  { problem := "discrete logarithms", name := "bsgs", ref := "Alg 5.3.1"
    param := "bits of the prime p", bound := "O(√p) products and table operations"
    growth := .exp 0.5, sizes := steps 34 42 2
    prepare := fun k ↦ do
      let ps := (List.range 8).map fun i ↦ randPrime (10 * k + i) k
      task (ps.map fun p ↦ (p, powMod 3 (randBelow k p) p)) fun ins ↦
        ins.map fun (p, t) ↦ bsgs p 3 t p },
  { problem := "discrete logarithms", name := "rhoLog", ref := "§5.2.2"
    param := "bits of the prime order N (p = 2N + 1)", bound := "T passes, T ≈ √N (heuristic)"
    growth := .exp 0.5, sizes := steps 34 42 2
    prepare := fun k ↦ do
      let Ns := (List.range 8).map fun i ↦ randSophieGermain (10 * k + i) k
      task (Ns.map fun N ↦ (N, powMod 4 (randBelow k N) (2 * N + 1))) fun ins ↦
        ins.map fun (N, t) ↦ rhoLog (2 * N + 1) N 4 t (2 ^ (k / 2 + 8)) } ]

def allCases : List Case :=
  gcdCases ++ powerCases ++ crtCases ++ sqrtCases ++ isqrtCases ++ mulCases ++ polyFieldCases ++
    polyMulCases ++ multipointCases ++ sieveCases ++ primalityCases ++ factoringCases ++ dlogCases

end Bench
