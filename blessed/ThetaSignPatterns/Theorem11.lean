import ThetaSignPatterns.Modularity
import ThetaSignPatterns.CuspGrowth
import ThetaSignPatterns.LocalConstants
import ThetaSignPatterns.MainTerm

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Theorem 1.1 and Corollary 1.2
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- The phase at the dominant cusp `(m-1)/(2m)`:
`Re(C_m^𝓁 e^{-2πin(m-1)/(2m)}) = (-1)ⁿ cos(π(φ_m 𝓁 - n/m))`. -/
theorem phase_11 (m ℓ n : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    (Codd m ^ ℓ * cexp (-(2 * π * I * n * ((((m : ℤ) - 1) / 2 : ℤ) : ℂ) / m))).re =
      (-1) ^ n * Real.cos (π * (phiM m * ℓ - n / m)) := by
  obtain ⟨t, rfl⟩ := hodd
  have ht : (((2 * t + 1 : ℕ) : ℤ) - 1) / 2 = t := by omega
  have hm0 : ((2 * t + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * t + 1 ≠ 0)
  have hI : -I = cexp (-(π / 2 * I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]
  have hneg : ((-1 : ℂ)) ^ n = cexp (n * (-(π * I))) := by
    rw [Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hm1 : (2 * (t : ℂ) + 1) ≠ 0 := by exact_mod_cast hm0
  have key : Codd (2 * t + 1) ^ ℓ *
      cexp (-(2 * π * I * n * (((((2 * t + 1 : ℕ) : ℤ) - 1) / 2 : ℤ) : ℂ) / (2 * t + 1 : ℕ))) =
      (((-1 : ℝ) ^ n : ℝ) : ℂ) *
        cexp (((-(π * (phiM (2 * t + 1) * ℓ - n / (2 * t + 1 : ℕ))) : ℝ) : ℂ) * I) := by
    rw [ht]
    push_cast
    rw [hneg]
    unfold Codd
    rw [hI, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold phiM
    push_cast
    field_simp
    ring
  rw [key, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem cos_phi_ne_zero (m ℓ n : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    Real.cos (π * (phiM m * ℓ - n / m)) ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp h
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hj' : phiM m * ℓ - n / m = (2 * j + 1) / 2 := by
    have hpi : π ≠ 0 := Real.pi_ne_zero
    apply mul_left_cancel₀ hpi
    rw [hj]; ring
  have e : ((m : ℝ) - 2) * ((m : ℝ) - 3) * ℓ - 2 * m * n =
      2 * (m : ℝ) ^ 2 * (phiM m * ℓ - n / m) := by
    unfold phiM; field_simp
  have hR : ((((m : ℤ) - 2) * ((m : ℤ) - 3) * ℓ - 2 * m * n : ℤ) : ℝ) =
      (((m : ℤ) ^ 2 * (2 * j + 1) : ℤ) : ℝ) := by
    push_cast; rw [e, hj']; ring
  have hZ : ((m : ℤ) - 2) * ((m : ℤ) - 3) * ℓ - 2 * m * n = (m : ℤ) ^ 2 * (2 * j + 1) :=
    by exact_mod_cast hR
  obtain ⟨t, rfl⟩ := hodd
  push_cast at hZ
  have h2 : (2 : ℤ) * ((2 * t - 1) * (t - 1) * ℓ - (2 * t + 1) * n - (2 * t ^ 2 + 2 * t) * (2 * j + 1)
      - j) = 1 := by linear_combination hZ
  generalize ((2 * (t : ℤ) - 1) * (t - 1) * ℓ - (2 * t + 1) * n - (2 * t ^ 2 + 2 * t) * (2 * j + 1)
      - j) = X at h2
  omega

/-- The cosine factor only depends on `n mod 2m`. -/
private theorem cos_phi_mod (m ℓ n : ℕ) (hm : 0 < m) :
    Real.cos (π * (phiM m * ℓ - n / m)) =
      Real.cos (π * (phiM m * ℓ - ((n % (2 * m) : ℕ) : ℝ) / m)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn : (n : ℝ) = ((n % (2 * m) : ℕ) : ℝ) + 2 * m * ((n / (2 * m) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n (2 * m)).symm
  have e : π * (phiM m * ℓ - n / m) =
      π * (phiM m * ℓ - ((n % (2 * m) : ℕ) : ℝ) / m) - ((n / (2 * m) : ℕ) : ℝ) * (2 * π) := by
    rw [hn]; field_simp; ring
  rw [e, Real.cos_sub_nat_mul_two_pi]

theorem cos_phi_bound (m ℓ : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, κ ≤ |Real.cos (π * (phiM m * ℓ - n / m))| := by
  obtain ⟨n₀, -, hn₀⟩ := (Finset.range (2 * m)).exists_min_image
    (fun n : ℕ => |Real.cos (π * (phiM m * ℓ - n / m))|) ⟨0, by simp; omega⟩
  refine ⟨_, abs_pos.mpr (cos_phi_ne_zero m ℓ n₀ hm hodd), fun n => ?_⟩
  rw [cos_phi_mod m ℓ n (by omega)]
  exact hn₀ _ (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))

/-- The dominant limit of `f_{m,𝓁}` at `h/m`, from that of `F_m`. -/
private theorem fMod_dom_tendsto (H : ExternalResults) (m ℓ : ℕ) (hm : 3 ≤ m) (h : ℤ) (L : ℂ)
    (hF : Tendsto (fun z : ℝ => Fan m (cexp (2 * π * I * ((h : ℂ) + I * z) / m)) *
        cexp (-((m * LamOdd m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun z : ℝ => fMod m ℓ ((h + I * z) / m) *
        cexp (-((ℓ * LamOdd m * m / z : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (cexp (2 * π * I * deltaMod m ℓ * h / m) * L ^ ℓ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcont : Tendsto (fun z : ℝ => cexp (2 * π * I * deltaMod m ℓ * ((h + I * z) / m)))
      (𝓝[>] 0) (𝓝 (cexp (2 * π * I * deltaMod m ℓ * h / m))) := by
    have hc : Continuous (fun z : ℝ => cexp (2 * π * I * deltaMod m ℓ * ((h + I * z) / m))) := by
      fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    convert h0 using 2
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    congr 1
    ring
  refine (hcont.mul (hF.pow ℓ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : (0 : ℝ) < z := hz
  have him : 0 < (((h : ℂ) + I * z) / m).im := by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, one_mul, zero_add]
    exact div_pos hz' hmpos
  rw [fMod_eq H m ℓ hm _ him, mul_pow, ← Complex.exp_nat_mul]
  have e1 : 2 * π * I * (((h : ℂ) + I * z) / m) = 2 * π * I * ((h : ℂ) + I * z) / m := by ring
  have e2 : cexp (-((ℓ * LamOdd m * m / z : ℝ) : ℂ)) =
      cexp (ℓ * -((m * LamOdd m / z : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [e1, e2]
  ring

private theorem lamOdd_pos_of_three_lt (m : ℕ) (hm : 3 < m) : 0 < LamOdd m := by
  have hm' : (3 : ℝ) < m := by exact_mod_cast hm
  unfold LamOdd
  apply div_pos
  · apply mul_pos (mul_pos Real.pi_pos (by linarith)) (by linarith)
  · positivity

/-- **Theorem 1.1** (asymptotics). -/
theorem theorem_1_1 (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m) (hℓ : 0 < ℓ) :
    (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
      ((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) * (-1) ^ n *
        Real.cos (π * (phiM m * ℓ - n / m)) *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
        (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hm5 : 5 ≤ m := by obtain ⟨t, rfl⟩ := hodd; omega
  have hm3 : 3 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hΛ : 0 < (ℓ : ℝ) * LamOdd m := mul_pos hℓR (lamOdd_pos_of_three_lt m hm)
  have hlt : (ℓ : ℝ) * LamOdd' m < ℓ * LamOdd m :=
    mul_lt_mul_of_pos_left (LamOdd'_lt m hm5) hℓR
  have hsum : ((m : ℤ) - 1) / 2 + ((m : ℤ) + 1) / 2 = m := by
    obtain ⟨t, rfl⟩ := hodd; push_cast; omega
  have hne : ((m : ℤ) + 1) / 2 ≠ ((m : ℤ) - 1) / 2 := by
    obtain ⟨t, rfl⟩ := hodd; push_cast; omega
  have hpne : ((((m : ℤ) - 1) / 2, m) : ℤ × ℕ) ≠ (((m : ℤ) + 1) / 2, m) := by
    intro h; exact hne (congrArg Prod.fst h).symm
  -- the constants at the two dominant cusps
  let C : ℤ × ℕ → ℂ := fun p => cexp (2 * π * I * deltaMod m ℓ * p.1 / p.2) *
    (if p.1 = ((m : ℤ) - 1) / 2 then Codd m ^ ℓ else starRingEnd ℂ (Codd m ^ ℓ))
  have hdom : ∀ p ∈ domOdd m, Tendsto (fun z : ℝ => fMod m ℓ ((p.1 + I * z) / p.2) *
      cexp (-(((ℓ * LamOdd m) * p.2 / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (C p)) := by
    intro p hp
    simp only [domOdd, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · have := fMod_dom_tendsto H m ℓ hm3 _ _ (Fan_dom₁ H m hm5 hodd)
      convert this using 2
      simp [C]
    · have := fMod_dom_tendsto H m ℓ hm3 _ _ (Fan_dom₂ H m hm5 hodd)
      convert this using 2
      simp [C, hne, map_pow]
  have hnondom : ∀ p : ℤ × ℕ, IsReducedCusp p → p ∉ domOdd m → ∃ K : ℝ,
      ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), ‖fMod m ℓ ((p.1 + I * (z : ℂ)) / p.2)‖ ≤
        K * Real.exp ((ℓ * LamOdd' m) * p.2 / z) := by
    intro p hp hpD
    obtain ⟨h0, hlt', hgcd⟩ := hp
    have hk : 0 < p.2 := by omega
    obtain ⟨K, hK⟩ := fMod_cusp_bound H m ℓ hm3 hodd p.1 p.2 hk hgcd
    have hA := Acusp_le_LamOdd' m hm5 hodd p ⟨h0, hlt', hgcd⟩ hpD
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK, self_mem_nhdsWithin] with z hz hz0
    have hz' : (0 : ℝ) < z := hz0
    have hab : (ℓ : ℝ) * Acusp m p.1 p.2 / z ≤ (ℓ * LamOdd' m) * p.2 / z := by
      apply div_le_div_of_nonneg_right _ hz'.le
      calc (ℓ : ℝ) * Acusp m p.1 p.2 ≤ ℓ * (p.2 * LamOdd' m) :=
            mul_le_mul_of_nonneg_left hA hℓR.le
        _ = _ := by ring
    calc _ ≤ K * Real.exp (ℓ * Acusp m p.1 p.2 / z) := hz
      _ ≤ max K 0 * Real.exp (ℓ * Acusp m p.1 p.2 / z) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max K 0 * Real.exp ((ℓ * LamOdd' m) * p.2 / z) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) (le_max_right _ _)
  have hE := H.rademacherZuckerman (fMod m ℓ) (fun n => (coeffC m ℓ n : ℂ)) (deltaMod m ℓ)
    (ℓ * LamOdd m) (ℓ * LamOdd' m) (domOdd m) C (fMod_isWHModular H m ℓ hm3)
    (fun τ hτ => hasSum_fMod H m ℓ hm3 τ hτ) hΛ hlt (domOdd_reduced m hm3 hodd) hdom hnondom
  have ho : (fun n : ℕ => ((coeffC m ℓ n : ℝ) : ℂ) -
      (rzTerm (ℓ * LamOdd m) (deltaMod m ℓ) ((((m : ℤ) - 1) / 2), m)
          (cexp (2 * π * I * deltaMod m ℓ * ((((m : ℤ) - 1) / 2 : ℤ) : ℂ) / m) * Codd m ^ ℓ) n +
        rzTerm (ℓ * LamOdd m) (deltaMod m ℓ) ((((m : ℤ) + 1) / 2), m)
          (cexp (2 * π * I * deltaMod m ℓ * ((((m : ℤ) + 1) / 2 : ℤ) : ℂ) / m) *
            starRingEnd ℂ (Codd m ^ ℓ)) n))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) *
        Real.exp (Real.sqrt (8 * π * (ℓ * LamOdd m) * n))) := by
    refine hE.congr_left (fun n => ?_)
    simp only [domOdd]
    rw [Finset.sum_pair hpne]
    simp [C, hne]
  obtain ⟨κ, hκpos, hκ⟩ := cos_phi_bound m ℓ hm3 hodd
  have hu : ∀ n : ℕ, κ ≤
      |(Codd m ^ ℓ * cexp (-(2 * π * I * n * ((((m : ℤ) - 1) / 2 : ℤ) : ℂ) / m))).re| := by
    intro n
    rw [phase_11 m ℓ n hm3 hodd, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hκ n
  have hmain := two_cusp H (ℓ * LamOdd m) (deltaMod m ℓ) hΛ (((m : ℤ) - 1) / 2)
    (((m : ℤ) + 1) / 2) m (by omega) hsum (Codd m ^ ℓ) (fun n => (coeffC m ℓ n : ℝ)) κ hκpos hu ho
  refine hmain.congr_right (Filter.Eventually.of_forall (fun n => ?_))
  have hX : 2 * ((ℓ : ℝ) * LamOdd m) / π = (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m) := by
    unfold LamOdd; field_simp; ring
  have hY : Real.sqrt (8 * π * ((ℓ : ℝ) * LamOdd m) * n) =
      π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m) := by
    have : 8 * π * ((ℓ : ℝ) * LamOdd m) * n =
        π ^ 2 * (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m) := by
      unfold LamOdd; field_simp; ring
    rw [this, Real.sqrt_mul (sq_nonneg π), Real.sqrt_sq Real.pi_pos.le]
  simp only
  rw [phase_11 m ℓ n hm3 hodd, hX, hY, Real.rpow_neg (Nat.cast_nonneg n)]
  ring

/-- `sgn(c x) = sgn x` for `c > 0`. -/
private theorem sign_mul_of_pos_left (c x : ℝ) (hc : 0 < c) : Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

/-- `sgn((-1)ⁿ x) = (-1)ⁿ sgn x`. -/
private theorem sign_neg_one_pow_mul (n : ℕ) (x : ℝ) :
    Real.sign ((-1) ^ n * x) = (-1) ^ n * Real.sign x := by
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h]
  · simp
  · rw [neg_one_mul, neg_one_mul, Real.sign_neg]

/-- **Theorem 1.1** (sign): `sgn c^{[𝓁]}_m(n) = (-1)ⁿ sgn cos(π(φ_m 𝓁 - n/m))` for `n ≫ 1`. -/
theorem theorem_1_1_sign (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m)
    (hℓ : 0 < ℓ) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
      (-1) ^ n * Real.sign (Real.cos (π * (phiM m * ℓ - n / m))) := by
  have hm3 : 3 ≤ m := by omega
  have hm' : (3 : ℝ) < m := by exact_mod_cast hm
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h1 : 0 < 1 - 1 / (m : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h3 : 0 < 1 - 3 / (m : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hm'
  have hX : 0 < (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m) :=
    div_pos (mul_pos (mul_pos h1 h3) hℓR) (by linarith)
  -- the main term, regrouped as a positive factor times `(-1)ⁿ cos`
  have hre : ∀ n : ℕ, 1 ≤ n →
      ((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) * (-1) ^ n *
        Real.cos (π * (phiM m * ℓ - n / m)) *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
        (n : ℝ) ^ (3 / 4 : ℝ) =
      (((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
        (n : ℝ) ^ (3 / 4 : ℝ)) * ((-1) ^ n * Real.cos (π * (phiM m * ℓ - n / m))) ∧
      0 < ((1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ / (2 * m)) ^ (1 / 4 : ℝ) *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 - 3 / (m : ℝ)) * ℓ * n / m)) /
        (n : ℝ) ^ (3 / 4 : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨by ring, ?_⟩
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hX _) (Real.exp_pos _))
      (Real.rpow_pos_of_pos hnR _)
  have hev := sign_eventually_of_equiv _ _ (theorem_1_1 H m ℓ hm hodd hℓ) (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [(hre n hn).1]
    exact mul_ne_zero (hre n hn).2.ne'
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (cos_phi_ne_zero m ℓ n hm3 hodd)))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  rw [hn, (hre n hn1).1, sign_mul_of_pos_left _ _ (hre n hn1).2, sign_neg_one_pow_mul]

private theorem sign_cos_12_even (t s r : ℕ) (hℓ : 0 < s + s) (h6 : 6 * (s + s) < 2 * t + 1)
    (hr : r < 2 * (2 * t + 1)) :
    Real.sign (Real.cos (π * (phiM (2 * t + 1) * ((s + s : ℕ) : ℝ) - r / ((2 * t + 1 : ℕ) : ℝ)))) =
      (-1) ^ ((s + s) / 2 + chi (S1 (2 * t + 1) (s + s) r)) := by
  have hmR : ((2 * t + 1 : ℕ) : ℝ) = 2 * t + 1 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * t + 1 := by positivity
  have hrle : r ≤ 4 * t + 1 := by omega
  have hr' : (r : ℝ) ≤ 4 * t + 1 := by exact_mod_cast hrle
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  -- `ℓ = 2s`: `cos = (-1)^s cos(π u)`, `u = R/m - 3ℓ/m²`, `R = r + 5s`
  have hs : (s + s) / 2 = s := by omega
  have h6' : (12 * s : ℝ) < 2 * t + 1 := by exact_mod_cast (by omega : 12 * s < 2 * t + 1)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  rw [hs, pow_add]
  set u : ℝ := (((r : ℝ) + 5 * s) * (2 * t + 1) - 6 * s) / (2 * t + 1) ^ 2 with hu
  have hx : π * (phiM (2 * t + 1) * ((s + s : ℕ) : ℝ) - (r : ℝ) / ((2 * t + 1 : ℕ) : ℝ)) =
      s * π - π * u := by
    rw [hu]; unfold phiM; rw [hmR]; push_cast; field_simp; ring
  rw [hx, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, add_zero,
    sign_neg_one_pow_mul]
  congr 1
  have hS : S1 (2 * t + 1) (s + s) (r : ℤ) ↔ (t + 1 ≤ r + 5 * s ∧ r + 5 * s ≤ 3 * t + 1) := by
    unfold S1
    rw [if_pos ⟨s, rfl⟩]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have : ((t + 1 : ℕ) : ℚ) ≤ ((r + 5 * s : ℕ) : ℚ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((r + 5 * s : ℕ) : ℚ) ≤ ((3 * t + 1 : ℕ) : ℚ) := by push_cast; linarith
        exact_mod_cast this
    · rintro ⟨h1, h2⟩
      have h1' : ((t + 1 : ℕ) : ℚ) ≤ ((r + 5 * s : ℕ) : ℚ) := by exact_mod_cast h1
      have h2' : ((r + 5 * s : ℕ) : ℚ) ≤ ((3 * t + 1 : ℕ) : ℚ) := by exact_mod_cast h2
      push_cast at h1' h2'
      constructor <;> linarith
  unfold chi
  by_cases hS' : S1 (2 * t + 1) (s + s) (r : ℤ)
  · rw [if_pos hS', pow_one]
    obtain ⟨h1, h2⟩ := hS.mp hS'
    have h1' : (t : ℝ) + 1 ≤ r + 5 * s := by exact_mod_cast h1
    have h2' : (r : ℝ) + 5 * s ≤ 3 * t + 1 := by exact_mod_cast h2
    apply Real.sign_of_neg
    have ha : (1 : ℝ) / 2 < u := by
      rw [hu, lt_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h1') hM.le]
    have hb : u < (3 : ℝ) / 2 := by
      rw [hu, div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h2') hM.le]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · rw [if_neg hS', pow_zero]
    apply Real.sign_of_pos
    rcases not_and_or.mp (mt hS.mpr hS') with h | h
    · have h' : (r : ℝ) + 5 * s ≤ t := by exact_mod_cast (by omega : r + 5 * s ≤ t)
      have ha : 0 < u := by
        rw [hu]
        apply div_pos _ (by positivity)
        nlinarith [mul_nonneg hr0 hM.le]
      have hb : u < 1 / 2 := by
        rw [hu, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h') hM.le]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    · have h' : (3 * t + 2 : ℝ) ≤ r + 5 * s := by
        exact_mod_cast (by omega : 3 * t + 2 ≤ r + 5 * s)
      have ha : 3 / 2 < u := by
        rw [hu, lt_div_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h') hM.le]
      have hb : u < 5 / 2 := by
        rw [hu, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hr') hM.le]
      rw [← Real.cos_sub_two_pi]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]

private theorem sign_cos_12_odd (t s r : ℕ) (h6 : 6 * (2 * s + 1) < 2 * t + 1)
    (hr : r < 2 * (2 * t + 1)) :
    Real.sign (Real.cos (π * (phiM (2 * t + 1) * ((2 * s + 1 : ℕ) : ℝ) -
        r / ((2 * t + 1 : ℕ) : ℝ)))) =
      (-1) ^ ((2 * s + 1) / 2 + chi (S1 (2 * t + 1) (2 * s + 1) r)) := by
  have hmR : ((2 * t + 1 : ℕ) : ℝ) = 2 * t + 1 := by push_cast; ring
  have hM : (0 : ℝ) < 2 * t + 1 := by positivity
  have hrle : r ≤ 4 * t + 1 := by omega
  have hr' : (r : ℝ) ≤ 4 * t + 1 := by exact_mod_cast hrle
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  -- `ℓ = 2s+1`: `cos = (-1)^s sin(π v)`, `v = (2r+5ℓ)/(2m) - 3ℓ/m²`
  have hs : (2 * s + 1) / 2 = s := by omega
  have h6' : (6 * (2 * s + 1) : ℝ) < 2 * t + 1 := by
    exact_mod_cast (by omega : 6 * (2 * s + 1) < 2 * t + 1)
  have hs0 : (0 : ℝ) ≤ s := s.cast_nonneg
  rw [hs, pow_add]
  set v : ℝ := ((2 * (r : ℝ) + 5 * (2 * s + 1)) * (2 * t + 1) - 6 * (2 * s + 1)) /
    (2 * (2 * t + 1) ^ 2) with hv
  have hx : π * (phiM (2 * t + 1) * ((2 * s + 1 : ℕ) : ℝ) - (r : ℝ) / ((2 * t + 1 : ℕ) : ℝ)) =
      s * π + (π / 2 - π * v) := by
    rw [hv]; unfold phiM; rw [hmR]; push_cast; field_simp; ring
  rw [hx, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, sub_zero,
    Real.cos_pi_div_two_sub, sign_neg_one_pow_mul]
  congr 1
  have hS : S1 (2 * t + 1) (2 * s + 1) (r : ℤ) ↔
      (2 * t + 1 ≤ r + 5 * s + 2 ∧ r + 5 * s + 3 ≤ 4 * t + 2) := by
    unfold S1
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨s, rfl⟩)]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have : ((2 * t + 1 : ℕ) : ℚ) ≤ ((r + 5 * s + 2 : ℕ) : ℚ) := by push_cast; linarith
        have h := (by exact_mod_cast this : 2 * t + 1 ≤ r + 5 * s + 2)
        omega
      · have : ((r + 5 * s + 3 : ℕ) : ℚ) ≤ ((4 * t + 2 : ℕ) : ℚ) := by push_cast; linarith
        have h := (by exact_mod_cast this : r + 5 * s + 3 ≤ 4 * t + 2)
        omega
    · rintro ⟨h1, h2⟩
      have h1n : 2 * t + 1 ≤ r + 5 * s + 2 := by omega
      have h2n : r + 5 * s + 3 ≤ 4 * t + 2 := by omega
      have h1' : ((2 * t + 1 : ℕ) : ℚ) ≤ ((r + 5 * s + 2 : ℕ) : ℚ) := by exact_mod_cast h1n
      have h2' : ((r + 5 * s + 3 : ℕ) : ℚ) ≤ ((4 * t + 2 : ℕ) : ℚ) := by exact_mod_cast h2n
      push_cast at h1' h2'
      constructor <;> linarith
  unfold chi
  by_cases hS' : S1 (2 * t + 1) (2 * s + 1) (r : ℤ)
  · rw [if_pos hS', pow_one]
    obtain ⟨h1, h2⟩ := hS.mp hS'
    have h1' : (2 * t + 1 : ℝ) ≤ r + 5 * s + 2 := by exact_mod_cast h1
    have h2' : (r : ℝ) + 5 * s + 3 ≤ 4 * t + 2 := by exact_mod_cast h2
    apply Real.sign_of_neg
    have ha : 1 < v := by
      rw [hv, lt_div_iff₀ (by positivity)]
      linarith [mul_nonneg (sub_nonneg.mpr h1') hM.le]
    have hb : v < 2 := by
      rw [hv, div_lt_iff₀ (by positivity)]
      linarith [mul_nonneg (sub_nonneg.mpr h2') hM.le]
    have hpa := mul_lt_mul_of_pos_left ha Real.pi_pos
    have hpb := mul_lt_mul_of_pos_left hb Real.pi_pos
    rw [← Real.sin_sub_two_pi]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · linarith
  · rw [if_neg hS', pow_zero]
    apply Real.sign_of_pos
    rcases not_and_or.mp (mt hS.mpr hS') with h | h
    · have h' : (r : ℝ) + 5 * s + 2 ≤ 2 * t := by
        exact_mod_cast (by omega : r + 5 * s + 2 ≤ 2 * t)
      have ha : 0 < v := by
        rw [hv]
        apply div_pos _ (by positivity)
        have hL : (0 : ℝ) < 2 * s + 1 := by positivity
        have h5 : (0 : ℝ) < 5 * (2 * t + 1) - 6 := by linarith
        linarith [mul_nonneg hr0 hM.le, mul_pos hL h5]
      have hb : v < 1 := by
        rw [hv, div_lt_iff₀ (by positivity)]
        linarith [mul_nonneg (sub_nonneg.mpr h') hM.le]
      have hpa := mul_lt_mul_of_pos_left ha Real.pi_pos
      have hpb := mul_lt_mul_of_pos_left hb Real.pi_pos
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith
    · have h' : (4 * t : ℝ) ≤ r + 5 * s := by
        exact_mod_cast (by omega : 4 * t ≤ r + 5 * s)
      have ha : 2 < v := by
        rw [hv, lt_div_iff₀ (by positivity)]
        linarith [mul_nonneg (sub_nonneg.mpr h') hM.le]
      have hb : v < 3 := by
        rw [hv, div_lt_iff₀ (by positivity)]
        linarith [mul_nonneg (sub_nonneg.mpr hr') hM.le, mul_nonneg hs0 hM.le, mul_nonneg hM.le (sub_nonneg.mpr h6'.le)]
      rw [← Real.sin_sub_two_pi]
      have hpa := mul_lt_mul_of_pos_left ha Real.pi_pos
      have hpb := mul_lt_mul_of_pos_left hb Real.pi_pos
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith


theorem sign_cos_12 (m ℓ r : ℕ) (hm : 3 < m) (hodd : Odd m) (hℓ : 0 < ℓ) (h6 : 6 * ℓ < m)
    (hr : r < 2 * m) :
    Real.sign (Real.cos (π * (phiM m * ℓ - r / m))) = (-1) ^ (ℓ / 2 + chi (S1 m ℓ r)) := by
  obtain ⟨t, rfl⟩ := hodd
  rcases Nat.even_or_odd ℓ with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact sign_cos_12_even t s r hℓ h6 hr
  · exact sign_cos_12_odd t s r h6 hr

/-- **Corollary 1.2.** -/
theorem corollary_1_2 (H : ExternalResults) (m ℓ : ℕ) (hm : 3 < m) (hodd : Odd m) (hℓ : 0 < ℓ)
    (h6 : 6 * ℓ < m) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffC m ℓ n : ℝ) =
      (-1) ^ (n % (2 * m) + ℓ / 2 + chi (S1 m ℓ (n % (2 * m) : ℕ))) := by
  filter_upwards [theorem_1_1_sign H m ℓ hm hodd hℓ] with n hn
  have hpar : ((-1 : ℝ)) ^ n = (-1) ^ (n % (2 * m)) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n % (2 * m)),
      Nat.mod_mod_of_dvd n (dvd_mul_right 2 m)]
  rw [hn, cos_phi_mod m ℓ n (by omega),
    sign_cos_12 m ℓ (n % (2 * m)) hm hodd hℓ h6 (Nat.mod_lt _ (by omega)), hpar, ← pow_add,
    add_assoc]

end ThetaSignPatterns
