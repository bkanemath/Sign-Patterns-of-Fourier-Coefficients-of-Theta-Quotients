import ThetaSignPatterns.ThetaProduct
import ThetaSignPatterns.DominantCusps

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Leading constants at the dominant cusps (Lemmas 3.3 and 5.3)
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- Quotient of two theta asymptotics (E3.3): for `b, b' ∈ (0,1)`,
`ϑ(aiz+b; iz)/ϑ(a'iz+b'; iz) · e^{-K/z}` tends to the ratio of the phases, where
`K = π(b(1-b) - b'(1-b'))`. -/
private theorem theta_ratio_tendsto (H : ExternalResults) (a b a' b' K : ℝ) (hb0 : 0 < b)
    (hb1 : b < 1) (hb0' : 0 < b') (hb1' : b' < 1) (hK : K = (b - b ^ 2 - (b' - b' ^ 2)) * π) :
    Tendsto (fun z : ℝ => theta (a * I * z + b) (I * z) / theta (a' * I * z + b') (I * z) *
        cexp (-((K / z : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (cexp (-(2 * π * I * a * b) + π * I * a) /
        cexp (-(2 * π * I * a' * b') + π * I * a'))) := by
  have h1 := H.thetaAsymp3 a b hb0 hb1
  have h2 := H.thetaAsymp3 a' b' hb0' hb1'
  have h3 := (h1.div h2).mul (IsEquivalent.refl (u := fun z : ℝ => cexp (-((K / z : ℝ) : ℂ))))
  refine h3.symm.tendsto_nhds ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz : (0 : ℝ) < z := hz
  have hs : ((Real.sqrt z : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne'
  have hE : cexp (((-b ^ 2 - 1 / 4 + b) * π / z : ℝ)) / cexp (((-b' ^ 2 - 1 / 4 + b') * π / z : ℝ))
      * cexp (-((K / z : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    rw [hK]; push_cast
    field_simp
    ring
  simp only [Pi.div_apply, Pi.mul_apply]
  have hc1 := Complex.exp_ne_zero (-(2 * π * I * a' * b') + π * I * a')
  have he1 := Complex.exp_ne_zero (((-b' ^ 2 - 1 / 4 + b') * π / z : ℝ))
  symm
  calc _ = cexp (-(2 * π * I * a * b) + π * I * a) / cexp (-(2 * π * I * a' * b') + π * I * a') *
        (cexp (((-b ^ 2 - 1 / 4 + b) * π / z : ℝ)) / cexp (((-b' ^ 2 - 1 / 4 + b') * π / z : ℝ))
          * cexp (-((K / z : ℝ) : ℂ))) := by
        field_simp
    _ = _ := by rw [hE, mul_one]

/-- `|e^{2πi(h+iz)/m}| < 1` for `z > 0`. -/
private theorem norm_q_lt_one (m : ℕ) (hm : 0 < m) (h : ℤ) (z : ℝ) (hz : 0 < z) :
    ‖cexp (2 * π * I * ((h : ℂ) + I * z) / m)‖ < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have : 2 * π * I * ((h : ℂ) + I * z) / m =
      ((-(2 * π * z / m) : ℝ) : ℂ) + ((2 * π * h / m : ℝ) : ℂ) * I := by
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [this, norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]
  have : 0 < 2 * π * z / m := by positivity
  linarith

/-- If `h₁ + h₂ = m`, then `e^{2πi(h₂+iz)/m}` is the conjugate of `e^{2πi(h₁+iz)/m}`. -/
private theorem q_conj (m : ℕ) (hm : 0 < m) (h₁ h₂ : ℤ) (hsum : (h₁ : ℂ) + h₂ = m) (z : ℝ) :
    cexp (2 * π * I * ((h₂ : ℂ) + I * z) / m) =
      starRingEnd ℂ (cexp (2 * π * I * ((h₁ : ℂ) + I * z) / m)) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.exp_conj, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  have h2 : (h₂ : ℂ) = m - h₁ := by rw [← hsum]; ring
  simp only [map_div₀, map_mul, map_add, map_ofNat, conj_ofReal, conj_I, map_intCast,
    map_natCast, h2]
  field_simp
  ring

/-- The second dominant cusp from the first, by complex conjugation. -/
private theorem dom₂_of_dom₁ (G : ℂ → ℂ)
    (hG : ∀ q : ℂ, ‖q‖ < 1 → G (starRingEnd ℂ q) = starRingEnd ℂ (G q))
    (m : ℕ) (hm : 0 < m) (h₁ h₂ : ℤ) (hsum : (h₁ : ℂ) + h₂ = m) (L : ℝ) (c : ℂ)
    (h : Tendsto (fun z : ℝ => G (cexp (2 * π * I * ((h₁ : ℂ) + I * z) / m)) *
        cexp (-((m * L / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun z : ℝ => G (cexp (2 * π * I * ((h₂ : ℂ) + I * z) / m)) *
        cexp (-((m * L / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (starRingEnd ℂ c)) := by
  refine ((continuous_conj.tendsto c).comp h).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz : (0 : ℝ) < z := hz
  simp only [Function.comp_apply, map_mul]
  rw [q_conj m hm h₁ h₂ hsum z, hG _ (norm_q_lt_one m hm h₁ z hz), ← Complex.exp_conj]
  congr 2
  simp [conj_ofReal]

/-- **Lemma 3.3**, `h = (m-1)/2`. -/
theorem Fan_dom₁ (H : ExternalResults) (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    Tendsto (fun z : ℝ => Fan m (cexp (2 * π * I * (((((m : ℤ) - 1) / 2 : ℤ) : ℂ) + I * z) / m)) *
        cexp (-((m * LamOdd m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (Codd m)) := by
  obtain ⟨k, hk⟩ := hodd
  have hh : ((m : ℤ) - 1) / 2 = (k : ℤ) := by omega
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hkC : (m : ℂ) = 2 * k + 1 := by exact_mod_cast hk
  have h1m : 1 / (m : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hmR
  have h1m' : 0 < 1 / (m : ℝ) := by positivity
  set b₁ : ℝ := 1 / 2 - (1 / m) / 2 with hb₁
  set b₂ : ℝ := 1 - 1 / m with hb₂
  have hT := theta_ratio_tendsto H (1 / m) b₁ (2 / m) b₂ (m * LamOdd m) (by linarith)
    (by linarith) (by linarith) (by linarith) (by simp only [hb₁, hb₂, LamOdd]; field_simp; ring)
  have hP : Tendsto (fun z : ℝ => cexp (-(π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁)))) (𝓝[>] 0)
      (𝓝 (cexp (-(π * I * b₁)))) := by
    have hc : Continuous (fun z : ℝ => cexp (-(π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁)))) := by
      fun_prop
    convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 2
    simp
  have hlim : Codd m = cexp (-(π * I * b₁)) *
      (cexp (-(2 * π * I * ((1 / m : ℝ) : ℂ) * b₁) + π * I * ((1 / m : ℝ) : ℂ)) /
        cexp (-(2 * π * I * ((2 / m : ℝ) : ℂ) * b₂) + π * I * ((2 / m : ℝ) : ℂ))) := by
    have hI : -I = cexp (-(π / 2 * I)) := by
      rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
    rw [Codd, ← Complex.exp_sub, ← Complex.exp_add, hI, ← Complex.exp_add]
    congr 1
    simp only [hb₁, hb₂]
    push_cast
    field_simp
    ring
  rw [hlim]
  refine (hP.mul hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz : (0 : ℝ) < z := hz
  have hw : 2 * π * I * (((((m : ℤ) - 1) / 2 : ℤ) : ℂ) + I * z) / m =
      2 * π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁) := by
    rw [hh, mul_div_assoc]
    congr 1
    simp only [hb₁]
    push_cast
    field_simp
    linear_combination -hkC
  have hw2 : 2 * (((1 / m : ℝ) : ℂ) * I * z + b₁) = ((2 / m : ℝ) : ℂ) * I * z + b₂ := by
    simp only [hb₁, hb₂]
    push_cast
    ring
  rw [hw, Fan_eq_theta H m (by omega) _ (I * z) ?_ ?_, hw2]
  · ring
  · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_re]
    simp
    positivity
  · refine ⟨k, ?_⟩
    simp only [hb₁]
    push_cast
    field_simp
    linear_combination hkC

/-- **Lemma 3.3**, `h = (m+1)/2`. -/
theorem Fan_dom₂ (H : ExternalResults) (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    Tendsto (fun z : ℝ => Fan m (cexp (2 * π * I * (((((m : ℤ) + 1) / 2 : ℤ) : ℂ) + I * z) / m)) *
        cexp (-((m * LamOdd m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (starRingEnd ℂ (Codd m))) := by
  obtain ⟨k, hk⟩ := hodd
  refine dom₂_of_dom₁ (Fan m) (Fan_conj m (by omega)) m (by omega) (((m : ℤ) - 1) / 2)
    (((m : ℤ) + 1) / 2) ?_ (LamOdd m) (Codd m) (Fan_dom₁ H m hm ⟨k, hk⟩)
  have h1 : ((m : ℤ) - 1) / 2 = k := by omega
  have h2 : ((m : ℤ) + 1) / 2 = k + 1 := by omega
  rw [h1, h2, hk]
  push_cast
  ring

private theorem mod_six_of_coprime (m : ℕ) (hcop : Nat.Coprime m 6) : m % 6 = 1 ∨ m % 6 = 5 := by
  have key : Nat.gcd (m % 6) 6 = 1 := by
    have : Nat.gcd m 6 = 1 := hcop
    rwa [Nat.gcd_comm, Nat.gcd_rec] at this
  have hlt := Nat.mod_lt m (show 6 > 0 by norm_num)
  generalize m % 6 = r at *
  interval_cases r <;> first | (left; rfl) | (right; rfl) | (exfalso; revert key; decide)

private theorem epsM_sq (m : ℕ) : epsM m ^ 2 = 1 := by unfold epsM; split_ifs <;> norm_num

private theorem epsM_bounds (m : ℕ) : -1 ≤ epsM m ∧ epsM m ≤ 1 := by
  unfold epsM; split_ifs <;> norm_num

private theorem epsZ_cast (m : ℕ) : ((epsZ m : ℤ) : ℂ) = (epsM m : ℂ) := by
  unfold epsZ epsM; split_ifs <;> simp

private theorem cast_h_tan₁ (m : ℕ) (hcop : Nat.Coprime m 6) :
    (((((m : ℤ) - epsZ m) / 6 : ℤ)) : ℂ) = ((m : ℂ) - (epsM m : ℂ)) / 6 := by
  have hdiv : (6 : ℤ) ∣ (m : ℤ) - epsZ m := by
    rcases mod_six_of_coprime m hcop with h | h <;> simp [epsZ, h] <;> omega
  have h' : (((((m : ℤ) - epsZ m) / 6 * 6 : ℤ)) : ℂ) = (((m : ℤ) - epsZ m : ℤ) : ℂ) := by
    rw [Int.ediv_mul_cancel hdiv]
  rw [eq_div_iff (by norm_num), ← epsZ_cast]
  push_cast at h' ⊢
  exact h'

private theorem cast_h_tan₂ (m : ℕ) (hcop : Nat.Coprime m 6) :
    ((((5 * (m : ℤ) + epsZ m) / 6 : ℤ)) : ℂ) = (5 * (m : ℂ) + (epsM m : ℂ)) / 6 := by
  have hdiv : (6 : ℤ) ∣ 5 * (m : ℤ) + epsZ m := by
    rcases mod_six_of_coprime m hcop with h | h <;> simp [epsZ, h] <;> omega
  have h' : ((((5 * (m : ℤ) + epsZ m) / 6 * 6 : ℤ)) : ℂ) = ((5 * (m : ℤ) + epsZ m : ℤ) : ℂ) := by
    rw [Int.ediv_mul_cancel hdiv]
  rw [eq_div_iff (by norm_num), ← epsZ_cast]
  push_cast at h' ⊢
  exact h'

/-- **Lemma 5.3**, `h = (m∓1)/6`. -/
theorem Ftan_dom₁ (H : ExternalResults) (m : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) :
    Tendsto (fun z : ℝ =>
        Ftan m (cexp (2 * π * I * (((((m : ℤ) - epsZ m) / 6 : ℤ) : ℂ) + I * z) / m)) *
        cexp (-((m * LamT m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (CT m)) := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hε2 := epsM_sq m
  obtain ⟨hεl, hεu⟩ := epsM_bounds m
  set ε := epsM m with hε
  set b₁ : ℝ := (m - ε) / (6 * m) with hb₁
  set b₂ : ℝ := 2 * b₁ with hb₂
  have hb₁0 : 0 < b₁ := div_pos (by linarith) (by positivity)
  have hb₁1 : b₁ < 1 / 2 := by rw [hb₁, div_lt_iff₀ (by positivity)]; linarith
  have hT := theta_ratio_tendsto H (2 / m) b₂ (1 / m) b₁ (m * LamT m) (by linarith)
    (by linarith) hb₁0 (by linarith) (by
      simp only [hb₁, hb₂, LamT]
      field_simp
      linear_combination 36 * hε2)
  have hP : Tendsto (fun z : ℝ => cexp (π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁))) (𝓝[>] 0)
      (𝓝 (cexp (π * I * b₁))) := by
    have hc : Continuous (fun z : ℝ => cexp (π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁))) := by
      fun_prop
    convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 2
    simp
  have hlim : CT m = cexp (π * I * b₁) *
      (cexp (-(2 * π * I * ((2 / m : ℝ) : ℂ) * b₂) + π * I * ((2 / m : ℝ) : ℂ)) /
        cexp (-(2 * π * I * ((1 / m : ℝ) : ℂ) * b₁) + π * I * ((1 / m : ℝ) : ℂ))) := by
    rw [CT, ← Complex.exp_sub, ← Complex.exp_add]
    congr 1
    simp only [hb₁, hb₂]
    push_cast
    field_simp
    ring
  rw [hlim]
  refine (hP.mul hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz : (0 : ℝ) < z := hz
  have hw : 2 * π * I * (((((m : ℤ) - epsZ m) / 6 : ℤ) : ℂ) + I * z) / m =
      2 * π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁) := by
    rw [cast_h_tan₁ m hcop, mul_div_assoc]
    congr 1
    simp only [hb₁]
    push_cast
    field_simp
    ring
  have hw2 : 2 * (((1 / m : ℝ) : ℂ) * I * z + b₁) = ((2 / m : ℝ) : ℂ) * I * z + b₂ := by
    simp only [hb₂]
    push_cast
    ring
  have hq := norm_q_lt_one m (by omega) (((m : ℤ) - epsZ m) / 6) z hz
  rw [Ftan_eq_inv m (by omega) _ hq, hw, Fan_eq_theta H m (by omega) _ (I * z) ?_ ?_, hw2]
  · rw [Complex.exp_neg (π * I * (((1 / m : ℝ) : ℂ) * I * z + b₁))]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_re]
    simp
    positivity
  · refine ⟨((m : ℤ) - epsZ m) / 6, ?_⟩
    rw [cast_h_tan₁ m hcop]
    simp only [hb₁]
    push_cast
    field_simp
    ring

/-- **Lemma 5.3**, `h = (5m±1)/6`. -/
theorem Ftan_dom₂ (H : ExternalResults) (m : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) :
    Tendsto (fun z : ℝ =>
        Ftan m (cexp (2 * π * I * ((((5 * (m : ℤ) + epsZ m) / 6 : ℤ) : ℂ) + I * z) / m)) *
        cexp (-((m * LamT m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (starRingEnd ℂ (CT m))) := by
  refine dom₂_of_dom₁ (Ftan m) (Ftan_conj m (by omega)) m (by omega) (((m : ℤ) - epsZ m) / 6)
    ((5 * (m : ℤ) + epsZ m) / 6) ?_ (LamT m) (CT m) (Ftan_dom₁ H m hm hcop)
  rw [cast_h_tan₁ m hcop, cast_h_tan₂ m hcop]
  ring

end ThetaSignPatterns
