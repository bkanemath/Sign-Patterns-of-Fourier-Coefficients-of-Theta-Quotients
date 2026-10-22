import ThetaSignPatterns.Formal

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Lemma 4.1: nonnegativity and monotonicity of `(-1)ⁿ c^{[𝓁]}_m(n)` for even `m`
-/

open PowerSeries

namespace ThetaSignPatterns

/-- A power series over `ℤ` with nonnegative coefficients. -/
def CoeffNonneg (φ : PowerSeries ℤ) : Prop := ∀ k, 0 ≤ coeff k φ

lemma CoeffNonneg.one : CoeffNonneg 1 := by
  intro k
  rw [coeff_one]
  split_ifs <;> norm_num

lemma CoeffNonneg.mul {a b : PowerSeries ℤ} (ha : CoeffNonneg a) (hb : CoeffNonneg b) :
    CoeffNonneg (a * b) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (ha _) (hb _)

lemma CoeffNonneg.pow {a : PowerSeries ℤ} (ha : CoeffNonneg a) (n : ℕ) :
    CoeffNonneg (a ^ n) := by
  induction n with
  | zero => simpa using CoeffNonneg.one
  | succ n ih => rw [pow_succ]; exact ih.mul ha

lemma CoeffNonneg.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∏ i ∈ s, f i) :=
  Finset.prod_induction _ CoeffNonneg (fun _ _ => CoeffNonneg.mul) CoeffNonneg.one h

/-- `σ(1 - X^e) = 1 + X^e` for odd `e`. -/
lemma coeffNonneg_rescale_oneSubPS {e : ℕ} (he : Odd e) :
    CoeffNonneg (rescale (-1 : ℤ) (oneSubPS e)) := by
  intro k
  rw [coeff_rescale]
  simp only [oneSubPS, map_sub, coeff_one, coeff_X_pow]
  by_cases h : k = e
  · subst h
    have : k ≠ 0 := by rintro rfl; simp at he
    simp [this, he.neg_one_pow]
  · by_cases h0 : k = 0
    · subst h0; simp [h]
    · simp [h, h0]

/-- `σ(g_e) = g_e` for even `e`. -/
lemma coeffNonneg_rescale_geomPS {e : ℕ} (he : Even e) :
    CoeffNonneg (rescale (-1 : ℤ) (geomPS e)) := by
  intro k
  rw [coeff_rescale]
  simp only [geomPS, coeff_mk]
  split_ifs with h
  · rw [(even_iff_two_dvd.2 (he.two_dvd.trans h)).neg_one_pow]; norm_num
  · simp

lemma coeffNonneg_rescale_factorF {m : ℕ} (hm : 4 ≤ m) (hev : Even m) (j : ℕ) :
    CoeffNonneg (rescale (-1 : ℤ) (factorF m j)) := by
  obtain ⟨t, rfl⟩ := hev
  have h2 : (t + t) * j = 2 * (t * j) := by ring
  unfold factorF
  simp only [map_mul]
  refine ((coeffNonneg_rescale_oneSubPS ?_).mul (coeffNonneg_rescale_oneSubPS ?_)).mul
    (coeffNonneg_rescale_geomPS ?_) |>.mul (coeffNonneg_rescale_geomPS ?_)
  · exact ⟨t * j, by omega⟩
  · exact ⟨t * j + t - 1, by omega⟩
  · exact ⟨t * j + 1, by omega⟩
  · exact ⟨t * j + t - 1, by omega⟩

/-- `(1 - X^e) g_e = 1`. -/
lemma oneSubPS_mul_geomPS {e : ℕ} (he : 1 ≤ e) : oneSubPS e * geomPS e = 1 := by
  ext k
  simp only [oneSubPS, sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomPS, coeff_mk,
    coeff_one]
  by_cases hk : e ≤ k
  · have hd : e ∣ k ↔ e ∣ k - e := by
      conv_lhs => rw [show k = (k - e) + e by omega]
      exact Nat.dvd_add_self_right
    have hk0 : k ≠ 0 := by omega
    simp only [hk, if_true, hk0, if_false, hd]
    split_ifs <;> simp
  · simp only [hk, if_false, sub_zero]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have : ¬ e ∣ k := fun hd => hk (Nat.le_of_dvd hk0 hd)
      simp [this, hk0.ne']

/-- `(1 - X) σ(1 - X) σ(g₂) = (1 - X)(1 + X) g₂ = 1`. -/
lemma one_sub_X_mul_rescale_aux :
    (1 - X) * rescale (-1 : ℤ) (oneSubPS 1) * rescale (-1 : ℤ) (geomPS 2) = 1 := by
  have h1 : rescale (-1 : ℤ) (oneSubPS 1) = 1 + X := by
    simp [oneSubPS, rescale_X]
  have h2 : rescale (-1 : ℤ) (geomPS 2) = geomPS 2 := by
    ext k
    rw [coeff_rescale]
    simp only [geomPS, coeff_mk]
    split_ifs with h
    · rw [(even_iff_two_dvd.2 h).neg_one_pow]; norm_num
    · simp
  rw [h1, h2]
  calc (1 - X) * (1 + X) * geomPS 2 = oneSubPS 2 * geomPS 2 := by simp only [oneSubPS]; ring
    _ = 1 := oneSubPS_mul_geomPS (by norm_num)

/-- `(-1)ⁿ c(n)` is the `n`-th coefficient of `σ((∏_{j<N} U_{m,j})^𝓁)` for `N > n`. -/
lemma neg_one_pow_mul_coeffC (m ℓ n N : ℕ) (hm : 1 ≤ m) (hN : n < N) :
    (-1 : ℤ) ^ n * coeffC m ℓ n =
      coeff n (rescale (-1 : ℤ) ((∏ j ∈ Finset.range N, factorF m j) ^ ℓ)) := by
  rw [coeff_rescale, coeffC_eq_partial m ℓ n N hm hN]

/-- **Lemma 4.1** (nonnegativity). -/
theorem lemma_4_1_nonneg (m ℓ n : ℕ) (hm : 4 ≤ m) (hev : Even m) :
    0 ≤ (-1 : ℝ) ^ n * (coeffC m ℓ n : ℝ) := by
  have h := neg_one_pow_mul_coeffC m ℓ n (n + 1) (by omega) (Nat.lt_succ_self n)
  have hnn : CoeffNonneg (rescale (-1 : ℤ) ((∏ j ∈ Finset.range (n + 1), factorF m j) ^ ℓ)) := by
    rw [map_pow, map_prod]
    exact (CoeffNonneg.prod _ _ fun j _ => coeffNonneg_rescale_factorF hm hev j).pow ℓ
  have : (0 : ℤ) ≤ (-1 : ℤ) ^ n * coeffC m ℓ n := h ▸ hnn n
  exact_mod_cast this

/-- **Lemma 4.1** (monotonicity). -/
theorem lemma_4_1_mono (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (hℓ : 0 < ℓ) :
    Monotone (fun n : ℕ => (-1 : ℝ) ^ n * (coeffC m ℓ n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  set Q := rescale (-1 : ℤ) ((∏ j ∈ Finset.range (n + 2), factorF m j) ^ ℓ) with hQ
  have e0 := neg_one_pow_mul_coeffC m ℓ n (n + 2) (by omega) (by omega)
  have e1 := neg_one_pow_mul_coeffC m ℓ (n + 1) (n + 2) (by omega) (by omega)
  -- the coefficient of `X^{n+1}` in `(1 - X) Q`
  have hdiff : coeff (n + 1) ((1 - X) * Q) = coeff (n + 1) Q - coeff n Q := by
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]
  have hnn : CoeffNonneg ((1 - X) * Q) := by
    obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by omega⟩
    rw [hQ, Finset.prod_range_succ', map_pow, map_mul, map_prod]
    set B := ∏ j ∈ Finset.range (n + 1), rescale (-1 : ℤ) (factorF m (j + 1))
    set A := rescale (-1 : ℤ) (factorF m 0) with hA
    have hB : CoeffNonneg B :=
      CoeffNonneg.prod _ _ fun j _ => coeffNonneg_rescale_factorF hm hev (j + 1)
    have hA0 : CoeffNonneg A := coeffNonneg_rescale_factorF hm hev 0
    have h1A : (1 - X) * A = rescale (-1 : ℤ) (oneSubPS (m - 1)) *
        rescale (-1 : ℤ) (geomPS (m - 2)) := by
      rw [hA]
      simp only [factorF, mul_zero, zero_add, map_mul]
      calc (1 - X) * (rescale (-1 : ℤ) (oneSubPS 1) * rescale (-1 : ℤ) (oneSubPS (m - 1)) *
            rescale (-1 : ℤ) (geomPS 2) * rescale (-1 : ℤ) (geomPS (m - 2)))
          = ((1 - X) * rescale (-1 : ℤ) (oneSubPS 1) * rescale (-1 : ℤ) (geomPS 2)) *
            (rescale (-1 : ℤ) (oneSubPS (m - 1)) * rescale (-1 : ℤ) (geomPS (m - 2))) := by
            ring
        _ = _ := by rw [one_sub_X_mul_rescale_aux, one_mul]
    have h1A' : CoeffNonneg ((1 - X) * A) := by
      obtain ⟨t, rfl⟩ := hev
      rw [h1A]
      exact (coeffNonneg_rescale_oneSubPS ⟨t - 1, by omega⟩).mul
        (coeffNonneg_rescale_geomPS ⟨t - 1, by omega⟩)
    have : (1 - X) * (B * A) ^ (l + 1) = B ^ (l + 1) * A ^ l * ((1 - X) * A) := by ring
    rw [this]
    exact ((hB.pow _).mul (hA0.pow _)).mul h1A'
  have key : (-1 : ℤ) ^ n * coeffC m ℓ n ≤ (-1 : ℤ) ^ (n + 1) * coeffC m ℓ (n + 1) := by
    rw [e0, e1]
    have := hnn (n + 1)
    rw [hdiff] at this
    linarith
  exact_mod_cast key

/-- `c^{[𝓁]}_m(0) = 1` for `m ≥ 2`: every factor has constant coefficient `1`. -/
lemma coeffC_zero_of_two_le (m ℓ : ℕ) (hm : 2 ≤ m) : coeffC m ℓ 0 = 1 := by
  unfold coeffC
  have hc1 : ∀ e, 1 ≤ e → constantCoeff (oneSubPS e) = 1 := by
    intro e he
    simp [oneSubPS, zero_pow (by omega : e ≠ 0)]
  have hg : ∀ e, constantCoeff (geomPS e) = 1 := by
    intro e
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [geomPS]
  rw [Finset.prod_range_one, coeff_zero_eq_constantCoeff_apply, map_pow]
  simp only [factorF, map_mul, hg, mul_zero, zero_add, hc1 1 le_rfl, hc1 (m - 1) (by omega)]
  simp

/-- For `m = 1` the factor `1 - X^{m-1} = 1 - X⁰` vanishes, so `c^{[1]}_1(0) = 0`. -/
lemma coeffC_one_one_zero : coeffC 1 1 0 = 0 := by
  have h0 : factorF 1 0 = 0 := by simp [factorF, oneSubPS]
  rw [coeffC, Finset.prod_range_one, h0, pow_one, map_zero]

/-- `c^{[𝓁]}_m(0) = 1` for `m ≥ 2`. -/
theorem coeffC_zero (m ℓ : ℕ) (hm : 2 ≤ m) : coeffC m ℓ 0 = 1 :=
  coeffC_zero_of_two_le m ℓ hm

end ThetaSignPatterns
