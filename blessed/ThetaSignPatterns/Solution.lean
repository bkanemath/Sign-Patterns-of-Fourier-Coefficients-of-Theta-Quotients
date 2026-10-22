import ThetaSignPatterns.Main

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Solution

The whole formalization in one statement: given the cited external results
`H : ExternalResults` (E1–E6, `External.lean`), all six main results of the paper hold for
all admissible parameters. This file is the umbrella of the development; `#print axioms`
on `ThetaSignPatterns.solution` lists only Lean's standard axioms.
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- Theorems 1.1, 1.3, 1.5 and Corollaries 1.2, 1.4, 1.6, under the external results. -/
theorem solution (H : ExternalResults) :
    -- Theorem 1.1 (asymptotics)
    (∀ m ℓ : ℕ, 3 < m → Odd m → 0 < ℓ →
      (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
        ((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) * (-1) ^ n *
          Real.cos (π * (phiM m * ℓ - n / m)) *
          Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
          (n : ℝ) ^ (3 / 4 : ℝ))) ∧
    -- Theorem 1.1 (sign)
    (∀ m ℓ : ℕ, 3 < m → Odd m → 0 < ℓ →
      ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
        (-1) ^ n * Real.sign (Real.cos (π * (phiM m * ℓ - n / m)))) ∧
    -- Corollary 1.2
    (∀ m ℓ : ℕ, 3 < m → Odd m → 0 < ℓ → 6 * ℓ < m →
      ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
        (-1) ^ (n % (2 * m) + ℓ / 2 + chi (S1 m ℓ (n % (2 * m) : ℕ)))) ∧
    -- Theorem 1.3
    (∀ m ℓ : ℕ, 4 ≤ m → Even m → 0 < ℓ →
      (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
        (ℓ : ℝ) ^ (1 / 4 : ℝ) /
            (2 ^ ((ℓ : ℝ) + 5 / 4) * (m : ℝ) ^ (1 / 4 : ℝ) * Real.sin (2 * π / m) ^ ℓ) *
          (-1) ^ n * Real.exp (π * Real.sqrt (2 * ℓ * n / m)) / (n : ℝ) ^ (3 / 4 : ℝ))) ∧
    -- Corollary 1.4
    (∀ m ℓ : ℕ, 4 ≤ m → Even m → 0 < ℓ → ∀ n : ℕ, Real.sign (coeffC m ℓ n : ℝ) = (-1) ^ n) ∧
    -- Theorem 1.5 (asymptotics)
    (∀ m lam : ℕ, 3 < m → Nat.Coprime m 6 → 0 < lam →
      (fun n : ℕ => (coeffGamma m lam n : ℝ)) ~[atTop] (fun n : ℕ =>
        ((1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m)) ^ (1 / 4 : ℝ) * Tfun m lam n *
          Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m))) /
          (n : ℝ) ^ (3 / 4 : ℝ))) ∧
    -- Theorem 1.5 (sign)
    (∀ m lam : ℕ, 3 < m → Nat.Coprime m 6 → 0 < lam →
      ∀ᶠ n : ℕ in atTop, Real.sign (coeffGamma m lam n : ℝ) = Real.sign (Tfun m lam n)) ∧
    -- Corollary 1.6
    (∀ m lam : ℕ, 3 < m → (m % 6 = 1 ∨ m % 6 = 5) → 0 < lam → 2 * lam < m →
      ∀ r j : ℕ, r ≤ 2 * m - 1 → j ≤ 2 →
      ∀ᶠ n : ℕ in atTop, (n : ℤ) ≡ 3 * r + 2 * m * j [ZMOD 6 * m] →
        Real.sign (coeffGamma m lam n : ℝ) =
          (-1) ^ (r + lam / 6 + chi (S2 m lam r)) * (epsLam m lam : ℝ)) :=
  ⟨fun m ℓ h1 h2 h3 => Main.theorem_1_1 H m ℓ h1 h2 h3,
   fun m ℓ h1 h2 h3 => Main.theorem_1_1_sign H m ℓ h1 h2 h3,
   fun m ℓ h1 h2 h3 h4 => Main.corollary_1_2 H m ℓ h1 h2 h3 h4,
   fun m ℓ h1 h2 h3 => Main.theorem_1_3 H m ℓ h1 h2 h3,
   fun m ℓ h1 h2 h3 n => Main.corollary_1_4 m ℓ h1 h2 h3 n,
   fun m lam h1 h2 h3 => Main.theorem_1_5 H m lam h1 h2 h3,
   fun m lam h1 h2 h3 => Main.theorem_1_5_sign H m lam h1 h2 h3,
   fun m lam h1 h2 h3 h4 r j hr hj => Main.corollary_1_6 H m lam h1 h2 h3 h4 r j hr hj⟩

end ThetaSignPatterns
