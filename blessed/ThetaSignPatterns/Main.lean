import ThetaSignPatterns.Theorem11
import ThetaSignPatterns.Theorem13
import ThetaSignPatterns.Theorem15

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Main results

The six main results of the paper, stated in full:
Theorems 1.1, 1.3 and 1.5 and Corollaries 1.2, 1.4 and 1.6. Theorems 1.1 and 1.5 each come
in two parts, the asymptotics and the eventual sign.

* "Asymptotic" is Mathlib's `Asymptotics.IsEquivalent` along `atTop`, written `u ~[atTop] v`.
  It means `u - v = o(v)`.
* "For `n ≫ 1`" is `∀ᶠ n in atTop`.
* `sgn` is `Real.sign`, with values in `{-1, 0, 1}`.

Every result except Corollary 1.4 takes the external results E1–E6 as one hypothesis,
`H : ExternalResults` (see `External.lean`). Corollary 1.4 needs no external input.
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns.Main

open ThetaSignPatterns

/-- **Theorem 1.1 (asymptotics).** -/
theorem theorem_1_1 (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m) (hℓ : 0 < ℓ) :
    (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
      ((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) * (-1) ^ n *
        Real.cos (π * (phiM m * ℓ - n / m)) *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
        (n : ℝ) ^ (3 / 4 : ℝ)) := by
  apply ThetaSignPatterns.theorem_1_1 <;> assumption

/-- **Theorem 1.1 (sign).** -/
theorem theorem_1_1_sign (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m)
    (hℓ : 0 < ℓ) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
      (-1) ^ n * Real.sign (Real.cos (π * (phiM m * ℓ - n / m))) := by
  apply ThetaSignPatterns.theorem_1_1_sign <;> assumption

/-- **Corollary 1.2.** -/
theorem corollary_1_2 (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m) (hℓ : 0 < ℓ)
    (h6 : 6 * ℓ < m) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
      (-1) ^ (n % (2 * m) + ℓ / 2 + chi (S1 m ℓ (n % (2 * m) : ℕ))) := by
  apply ThetaSignPatterns.corollary_1_2 <;> assumption

/-- **Theorem 1.3.** -/
theorem theorem_1_3 (H : ExternalResults) (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (hℓ : 0 < ℓ) :
    (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
      (ℓ : ℝ) ^ (1 / 4 : ℝ) /
          (2 ^ ((ℓ : ℝ) + 5 / 4) * (m : ℝ) ^ (1 / 4 : ℝ) * Real.sin (2 * π / m) ^ ℓ) *
        (-1) ^ n * Real.exp (π * Real.sqrt (2 * ℓ * n / m)) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  apply ThetaSignPatterns.theorem_1_3 <;> assumption

/-- **Corollary 1.4.** -/
theorem corollary_1_4 (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (hℓ : 0 < ℓ) (n : ℕ) :
    Real.sign (coeffC m ℓ n : ℝ) = (-1) ^ n := by
  apply ThetaSignPatterns.corollary_1_4 <;> assumption

/-- **Theorem 1.5 (asymptotics).** -/
theorem theorem_1_5 (H : ExternalResults) (m lam : ℕ) (hm : 3 < m) (hcop : Nat.Coprime m 6)
    (hlam : 0 < lam) :
    (fun n : ℕ => (coeffGamma m lam n : ℝ)) ~[atTop] (fun n : ℕ =>
      ((1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m)) ^ (1 / 4 : ℝ) * Tfun m lam n *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m))) /
        (n : ℝ) ^ (3 / 4 : ℝ)) := by
  apply ThetaSignPatterns.theorem_1_5 <;> assumption

/-- **Theorem 1.5 (sign).** -/
theorem theorem_1_5_sign (H : ExternalResults) (m lam : ℕ) (hm : 3 < m)
    (hcop : Nat.Coprime m 6) (hlam : 0 < lam) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffGamma m lam n : ℝ) = Real.sign (Tfun m lam n) := by
  apply ThetaSignPatterns.theorem_1_5_sign <;> assumption

/-- **Corollary 1.6.** -/
theorem corollary_1_6 (H : ExternalResults) (m lam : ℕ) (hm : 3 < m)
    (hm6 : m % 6 = 1 ∨ m % 6 = 5) (hlam : 0 < lam) (h2 : 2 * lam < m) (r j : ℕ)
    (hr : r ≤ 2 * m - 1) (hj : j ≤ 2) :
    ∀ᶠ n : ℕ in atTop, (n : ℤ) ≡ 3 * r + 2 * m * j [ZMOD 6 * m] →
      Real.sign (coeffGamma m lam n : ℝ) =
        (-1) ^ (r + lam / 6 + chi (S2 m lam r)) * (epsLam m lam : ℝ) := by
  apply ThetaSignPatterns.corollary_1_6 <;> assumption

end ThetaSignPatterns.Main
