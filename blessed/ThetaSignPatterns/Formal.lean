import ThetaSignPatterns.Defs

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Formal power series: stabilisation of the coefficients

`coeffC m 𝓁 n` is defined from the product of the factors `j ≤ n`. Any longer product has
the same `n`-th coefficient, so `coeffC` is the coefficient of the infinite product.
-/

open PowerSeries

namespace ThetaSignPatterns

/-- `1 - X^e ≡ 1 (mod X^k)` for `k ≤ e`. -/
lemma X_pow_dvd_oneSubPS_sub_one {k e : ℕ} (h : k ≤ e) :
    (X : PowerSeries ℤ) ^ k ∣ oneSubPS e - 1 := by
  have : oneSubPS e - 1 = -(X ^ e) := by simp [oneSubPS]
  rw [this, dvd_neg]
  exact pow_dvd_pow X h

/-- `g_e ≡ 1 (mod X^k)` for `k ≤ e`. -/
lemma X_pow_dvd_geomPS_sub_one {k e : ℕ} (h : k ≤ e) :
    (X : PowerSeries ℤ) ^ k ∣ geomPS e - 1 := by
  rw [X_pow_dvd_iff]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [geomPS]
  · have : ¬ e ∣ i := fun hd => absurd (Nat.le_of_dvd hi0 hd) (by omega)
    simp [geomPS, coeff_one, this, hi0.ne']

lemma X_pow_dvd_mul_sub_one {k : ℕ} {a b : PowerSeries ℤ} (ha : X ^ k ∣ a - 1)
    (hb : X ^ k ∣ b - 1) : X ^ k ∣ a * b - 1 := by
  have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left ha b) hb

/-- If `f j ≡ 1 (mod X^{n+1})` for `j > n`, the `n`-th coefficient of `(∏_{j<N} f j)^ℓ`
does not depend on `N > n`. -/
lemma coeff_prod_pow_stable (f : ℕ → PowerSeries ℤ) (ℓ n N : ℕ) (hN : n < N)
    (hf : ∀ j, n < j → X ^ (n + 1) ∣ f j - 1) :
    coeff n ((∏ j ∈ Finset.range N, f j) ^ ℓ) =
      coeff n ((∏ j ∈ Finset.range (n + 1), f j) ^ ℓ) := by
  set I : Ideal (PowerSeries ℤ) := Ideal.span {X ^ (n + 1)}
  have h1 : ∀ j, n < j → Ideal.Quotient.mk I (f j) = 1 := by
    intro j hj
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hf j hj
  have key : Ideal.Quotient.mk I (∏ j ∈ Finset.range N, f j) =
      Ideal.Quotient.mk I (∏ j ∈ Finset.range (n + 1), f j) := by
    rw [map_prod, map_prod]
    symm
    apply Finset.prod_subset (Finset.range_subset_range.2 hN)
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    exact h1 j (by omega)
  have hd : X ^ (n + 1) ∣ (∏ j ∈ Finset.range N, f j) ^ ℓ -
      (∏ j ∈ Finset.range (n + 1), f j) ^ ℓ := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_pow, map_pow, key]
  have := (X_pow_dvd_iff.1 hd) n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at this

/-- The `n`-th coefficient of `(∏_{j<N} U_{m,j})^𝓁` is `c^{[𝓁]}_m(n)` once `N > n`. -/
theorem coeffC_eq_partial (m ℓ n N : ℕ) (hm : 1 ≤ m) (hN : n < N) :
    coeff n ((∏ j ∈ Finset.range N, factorF m j) ^ ℓ) = coeffC m ℓ n := by
  unfold coeffC
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- `m = 1`: the factor `j = 0` contains `1 - X⁰ = 0`.
    obtain rfl : m = 1 := by omega
    have h0 : factorF 1 0 = 0 := by simp [factorF, oneSubPS]
    rw [Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < N)) h0,
      Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < n + 1)) h0]
  · apply coeff_prod_pow_stable _ ℓ n N hN
    intro j hj
    have hmj : n + 1 ≤ m * j := le_trans (by omega) (Nat.mul_le_mul_right j hm2)
    unfold factorF
    refine X_pow_dvd_mul_sub_one (X_pow_dvd_mul_sub_one (X_pow_dvd_mul_sub_one ?_ ?_) ?_) ?_
    · exact X_pow_dvd_oneSubPS_sub_one (by omega)
    · exact X_pow_dvd_oneSubPS_sub_one (by omega)
    · exact X_pow_dvd_geomPS_sub_one (by omega)
    · exact X_pow_dvd_geomPS_sub_one (by omega)

/-- The `n`-th coefficient of `(∏_{j<N} Ũ_{m,j})^λ` is `γ^{[λ]}_m(n)` once `N > n`. -/
theorem coeffGamma_eq_partial (m lam n N : ℕ) (hm : 1 ≤ m) (hN : n < N) :
    coeff n ((∏ j ∈ Finset.range N, factorFt m j) ^ lam) = coeffGamma m lam n := by
  unfold coeffGamma
  rcases Nat.lt_or_ge m 3 with hm1 | hm3
  · -- `m ≤ 2`: the factor `j = 0` contains `1 - X⁰ = 0`.
    have h0 : factorFt m 0 = 0 := by
      have : m - 2 = 0 := by omega
      simp [factorFt, oneSubPS, this]
    rw [Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < N)) h0,
      Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < n + 1)) h0]
  · apply coeff_prod_pow_stable _ lam n N hN
    intro j hj
    have hmj : n + 1 ≤ m * j := le_trans (by omega) (Nat.mul_le_mul_right j (by omega : 1 ≤ m))
    unfold factorFt
    refine X_pow_dvd_mul_sub_one (X_pow_dvd_mul_sub_one (X_pow_dvd_mul_sub_one ?_ ?_) ?_) ?_
    · exact X_pow_dvd_oneSubPS_sub_one (by omega)
    · exact X_pow_dvd_oneSubPS_sub_one (by omega)
    · exact X_pow_dvd_geomPS_sub_one (by omega)
    · exact X_pow_dvd_geomPS_sub_one (by omega)

end ThetaSignPatterns
