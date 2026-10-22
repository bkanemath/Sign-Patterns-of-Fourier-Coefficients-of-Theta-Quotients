import ThetaSignPatterns.Defs

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Basic properties of `ϑ`

Lemma 2.2 (2) of the paper (elliptic quasi-periodicity), proved from the series.
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- `ϑ` in terms of Mathlib's `jacobiTheta₂`:
`ϑ(w;τ) = e^{πiτ/4 + πi(w+1/2)} θ₂(w + 1/2 + τ/2; τ)`. -/
theorem theta_eq_jacobiTheta₂ (w τ : ℂ) :
    theta w τ = cexp (π * I * τ / 4 + π * I * (w + 1 / 2)) * jacobiTheta₂ (w + 1 / 2 + τ / 2) τ := by
  unfold theta jacobiTheta₂
  rw [← tsum_mul_left]
  congr 1
  ext k
  rw [jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **Lemma 2.2 (2).** `ϑ(w + λτ + μ; τ) = (-1)^{λ+μ} q^{-λ²/2} ζ^{-λ} ϑ(w;τ)`, with
`q = e^{2πiτ}`, `ζ = e^{2πiw}`. -/
theorem theta_quasi (lam mu : ℤ) (w τ : ℂ) (hτ : 0 < τ.im) :
    theta (w + lam * τ + mu) τ =
      (-1 : ℂ) ^ (lam + mu) * cexp (-(π * I * (lam : ℂ) ^ 2 * τ)) *
        cexp (-(2 * π * I * lam * w)) * theta w τ := by
  have hsign : (-1 : ℂ) ^ (lam + mu) = cexp (((lam + mu : ℤ) : ℂ) * (π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hterm : ∀ k : ℤ,
      cexp (π * I * ((k : ℂ) + 1 / 2) ^ 2 * τ) *
          cexp (2 * π * I * ((k : ℂ) + 1 / 2) * (w + lam * τ + mu + 1 / 2)) =
        (-1 : ℂ) ^ (lam + mu) * cexp (-(π * I * (lam : ℂ) ^ 2 * τ)) *
          cexp (-(2 * π * I * lam * w)) *
          (cexp (π * I * (((k + lam : ℤ) : ℂ) + 1 / 2) ^ 2 * τ) *
            cexp (2 * π * I * (((k + lam : ℤ) : ℂ) + 1 / 2) * (w + 1 / 2))) := by
    intro k
    have h1 : cexp (((k * mu - lam : ℤ) : ℂ) * (2 * π * I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I _
    rw [hsign]
    refine Eq.trans ?_ ((congrArg (_ * ·) h1).trans (mul_one _))
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold theta
  simp_rw [hterm]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight lam).tsum_eq
    (fun n : ℤ => cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) *
      cexp (2 * π * I * ((n : ℂ) + 1 / 2) * (w + 1 / 2)))

end ThetaSignPatterns
