import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power

/-!
# §5.2.2 Pollard rho method for discrete logarithms

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.2.2.

* `rhoLog` — the rho method for the discrete logarithm of `t` to the base `g` in `Z_p^*`,
  where `g` has order `N`: iterate a pseudorandom map on triples `(x, a, b)` with
  `x = g^a t^b`, find `x_i = x_{2i}` by Floyd's method, and solve
  `(b_i - b_{2i}) l ≡ a_{2i} - a_i (mod N)`.
* `rhoLog_sound` — a returned `l` satisfies `g^l ≡ t (mod p)`.

Soundness is obtained by *checking* the candidate (`g^l mod p == t`) before returning it —
one extra modular power, which any careful implementation performs.  The book describes
the method in prose (there is no numbered algorithm); the three-way split by `x mod 3` is
the classical choice of pseudorandom map.

**Not proved:** that a collision occurs after `O(√N)` steps (the same random-map
heuristic as for factoring), and that the candidate passes the check (it does when the
congruence is solvable, i.e. `gcd(b_i - b_{2i}, N) = 1`).
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- One step of the pseudorandom walk on `(x, a, b)` with `x = g^a t^b`:
`x ↦ t x`, `x²` or `g x` according to `x mod 3`; the exponents are kept modulo `N`. -/
def rhoLogStep (p N g t : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (x, a, b) := s
  if x % 3 = 0 then (x * x % p, 2 * a % N, 2 * b % N)
  else if x % 3 = 1 then (t * x % p, a, (b + 1) % N)
  else (g * x % p, (a + 1) % N, b)

/-- From a collision `g^a t^b = g^A t^B`, the candidate logarithm
`l = (A - a) (b - B)⁻¹ mod N`. -/
def rhoLogSolve (N a b A B : ℕ) : ℕ :=
  (A + N - a % N) % N * modInv ((b + N - B % N) % N) N % N

/-- Floyd's cycle search for the walk; on a collision, return the candidate if it checks. -/
def rhoLogLoop (p N g t : ℕ) : (u v : ℕ × ℕ × ℕ) → ℕ → Option ℕ
  | _, _, 0 => none
  | u, v, fuel + 1 =>
    let u' := rhoLogStep p N g t u
    let v' := rhoLogStep p N g t (rhoLogStep p N g t v)
    if u'.1 = v'.1 then
      let l := rhoLogSolve N u'.2.1 u'.2.2 v'.2.1 v'.2.2
      if powMod g l p = t % p then some l else none
    else rhoLogLoop p N g t u' v' fuel

/-- **Pollard rho for discrete logarithms** in `Z_p^*`: `g` of order `N`, target `t`. -/
def rhoLog (p N g t fuel : ℕ) : Option ℕ :=
  rhoLogLoop p N g t (1 % p, 0, 0) (1 % p, 0, 0) fuel

theorem rhoLogLoop_sound {p N g t : ℕ} {u v : ℕ × ℕ × ℕ} {fuel l : ℕ}
    (h : rhoLogLoop p N g t u v fuel = some l) : powMod g l p = t % p := by
  induction fuel generalizing u v with
  | zero => simp [rhoLogLoop] at h
  | succ fuel ih =>
    simp only [rhoLogLoop] at h
    split_ifs at h with h₁ h₂
    · obtain rfl := Option.some.inj h
      exact h₂
    · exact ih h

/-- **Soundness of the rho method for discrete logarithms**: a returned `l` satisfies
`g^l ≡ t (mod p)`. -/
theorem rhoLog_sound {p N g t fuel l : ℕ} (h : rhoLog p N g t fuel = some l) :
    g ^ l ≡ t [MOD p] := by
  have := rhoLogLoop_sound h
  rwa [powMod_eq] at this

end PrimeNumbers.Chapter5
