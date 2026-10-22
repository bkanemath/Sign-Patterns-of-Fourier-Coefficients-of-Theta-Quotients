import ThetaSignPatterns.ThetaProduct
import ThetaSignPatterns.Lemma41

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Lemma 4.2, Theorem 1.3 and Corollary 1.4
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- Multiplication by a positive real maps the cone `R_Δ` into itself, continuously at `0`. -/
private lemma tendsto_mul_cone {c : ℝ} (hc : 0 < c) (Δ : ℝ) :
    Tendsto (fun z : ℂ => (c : ℂ) * z) (𝓝[cone Δ] 0) (𝓝[cone Δ] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun z : ℂ => (c : ℂ) * z) (𝓝 0) (𝓝 ((c : ℂ) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨h1, h2⟩ := hz
    refine ⟨by simpa using mul_pos hc h1, ?_⟩
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mul_re, sub_zero]
    rw [abs_mul, abs_of_pos hc]
    nlinarith

private lemma cpow_half_sq {x : ℂ} (hx : x ≠ 0) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [sq, ← cpow_add _ _ hx]; norm_num

private lemma inv_cpow_half {x : ℂ} (hx : 0 < x.re) :
    x⁻¹ ^ (1 / 2 : ℂ) = (x ^ (1 / 2 : ℂ))⁻¹ := by
  apply inv_cpow
  rw [Ne, arg_eq_pi_iff]; intro h; linarith [h.1]

/-- The algebra of the main terms in Lemma 4.2. -/
private lemma lemma_4_2_alg (z : ℂ) (hz : 0 < z.re) (M : ℝ) (hM : 0 < M) (s1 s2 : ℂ)
    (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) :
    -I * 1 * ((2 * π / (M * z)) ^ (1 / 2 : ℂ) * cexp (-(π ^ 2 / (6 * (M * z))))) ^ 2 *
        (-2 * I * s1 * cexp (-(π / (4 * (((M / π : ℝ) : ℂ) * z)))) /
          (((M / π : ℝ) : ℂ) * z) ^ (1 / 2 : ℂ)) /
      (((2 * π / (((2 * M : ℝ) : ℂ) * z)) ^ (1 / 2 : ℂ) *
          cexp (-(π ^ 2 / (6 * (((2 * M : ℝ) : ℂ) * z))))) *
        (-2 * I * s1 * cexp (-(π / (4 * (((M / (2 * π) : ℝ) : ℂ) * z)))) /
          (((M / (2 * π) : ℝ) : ℂ) * z) ^ (1 / 2 : ℂ)) *
        (-2 * I * s2 * cexp (-(π / (4 * (((M / (2 * π) : ℝ) : ℂ) * z)))) /
          (((M / (2 * π) : ℝ) : ℂ) * z) ^ (1 / 2 : ℂ))) =
      cexp (π ^ 2 / (2 * M * z)) / (2 * s2) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  have hM0 : (M : ℂ) ≠ 0 := ofReal_ne_zero.2 hM.ne'
  set Z1 : ℂ := ((M / (2 * π) : ℝ) : ℂ) * z with hZ1
  set Z2 : ℂ := ((M / π : ℝ) : ℂ) * z with hZ2
  have hZ1z : Z1 ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 (by positivity)) hz0
  have hZ2z : Z2 ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 (by positivity)) hz0
  have hZ2re : 0 < Z2.re := by
    rw [hZ2, re_ofReal_mul]; exact mul_pos (by positivity) hz
  have e1 : 2 * (π : ℂ) / (M * z) = Z1⁻¹ := by
    rw [hZ1]; push_cast; field_simp
  have e2 : 2 * (π : ℂ) / (((2 * M : ℝ) : ℂ) * z) = Z2⁻¹ := by
    rw [hZ2]; push_cast; field_simp
  have hexp : cexp (-(π ^ 2 / (6 * (M * z)))) ^ 2 * cexp (-(π / (4 * Z2))) =
      cexp (π ^ 2 / (2 * M * z)) * cexp (-(π ^ 2 / (6 * (((2 * M : ℝ) : ℂ) * z)))) *
        cexp (-(π / (4 * Z1))) * cexp (-(π / (4 * Z1))) := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [hZ1, hZ2]; push_cast; field_simp; ring
  rw [e1, e2, mul_pow, cpow_half_sq (inv_ne_zero hZ1z), inv_cpow_half hZ2re]
  have hp : (Z1 ^ (1 / 2 : ℂ)) ^ 2 = Z1 := cpow_half_sq hZ1z
  have hp0 : Z1 ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; rw [h] at hp; simp at hp; exact hZ1z hp.symm
  have hr0 : Z2 ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := cpow_half_sq hZ2z; rw [h] at this; simp at this; exact hZ2z this.symm
  have hE2 : cexp (-(π ^ 2 / (6 * (((2 * M : ℝ) : ℂ) * z)))) ≠ 0 := Complex.exp_ne_zero _
  have hE4 : cexp (-(π / (4 * Z1))) ≠ 0 := Complex.exp_ne_zero _
  generalize Z1 ^ (1 / 2 : ℂ) = p at hp hp0 ⊢
  generalize Z2 ^ (1 / 2 : ℂ) = r at hr0 ⊢
  generalize cexp (-(π ^ 2 / (6 * (M * z)))) = E1 at hexp ⊢
  generalize cexp (-(π / (4 * Z2))) = E3 at hexp ⊢
  generalize cexp (π ^ 2 / (2 * M * z)) = E0 at hexp ⊢
  generalize cexp (-(π ^ 2 / (6 * (((2 * M : ℝ) : ℂ) * z)))) = E2 at hexp hE2 ⊢
  generalize cexp (-(π / (4 * Z1))) = E4 at hexp hE4 ⊢
  have hI : Complex.I ^ 2 = -1 := I_sq
  rw [← hp]
  field_simp
  linear_combination hexp

/-- **Lemma 4.2.** `F_m(-e^{-z})^𝓁 ∼ e^{π²𝓁/(2mz)} / (2^𝓁 sin^𝓁(2π/m))` as `z → 0` in `R_Δ`. -/
theorem lemma_4_2 (H : ExternalResults) (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (Δ : ℝ)
    (hΔ : 0 ≤ Δ) :
    (fun z : ℂ => Fan m (-cexp (-z)) ^ ℓ) ~[𝓝[cone Δ] 0]
      (fun z : ℂ => cexp (π ^ 2 * ℓ / (2 * m * z)) / (2 ^ ℓ * (Real.sin (2 * π / m) : ℂ) ^ ℓ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  have ha : ∀ k : ℝ, 0 < k → k < 1 → ∀ n : ℤ, k ≠ n := by
    intro k h0 h1 n hn
    rw [hn] at h0 h1
    have : (0 : ℤ) < n := by exact_mod_cast h0
    have : n < 1 := by exact_mod_cast h1
    omega
  have ha1 : ∀ n : ℤ, (1 / m : ℝ) ≠ n :=
    ha _ (by positivity) (by rw [div_lt_one hm0]; linarith)
  have ha2 : ∀ n : ℤ, (2 / m : ℝ) ≠ n :=
    ha _ (by positivity) (by rw [div_lt_one hm0]; linarith)
  have hc1 : (0 : ℝ) < m / (2 * π) := by positivity
  have hc2 : (0 : ℝ) < m / π := by positivity
  have hT1 := (H.thetaAsymp4 _ ha1 Δ hΔ).comp_tendsto (tendsto_mul_cone hc1 Δ)
  have hT2 := (H.thetaAsymp4 _ ha2 Δ hΔ).comp_tendsto (tendsto_mul_cone hc1 Δ)
  have hT3 := (H.thetaAsymp4 _ ha1 Δ hΔ).comp_tendsto (tendsto_mul_cone hc2 Δ)
  have hA1 := (H.etaAsymp Δ hΔ).comp_tendsto (tendsto_mul_cone hm0 Δ)
  have hA2 := (H.etaAsymp Δ hΔ).comp_tendsto
    (tendsto_mul_cone (by positivity : (0 : ℝ) < 2 * m) Δ)
  have hE : (fun z : ℂ => cexp (z / 2)) ~[𝓝[cone Δ] 0] (fun _ => (1 : ℂ)) := by
    have : Tendsto (fun z : ℂ => cexp (z / 2)) (𝓝 0) (𝓝 (cexp (0 / 2))) :=
      ((continuous_id.div_const 2).cexp).tendsto 0
    exact (isEquivalent_const_iff_tendsto one_ne_zero).2
      (by simpa using this.mono_left nhdsWithin_le_nhds)
  have key := ((((IsEquivalent.refl (u := fun _ : ℂ => -I)).mul hE).mul (hA1.pow 2)).mul
    hT3).div ((hA2.mul hT1).mul hT2)
  have hF : (fun z : ℂ => Fan m (-cexp (-z))) ~[𝓝[cone Δ] 0]
      (fun z : ℂ => cexp (π ^ 2 / (2 * m * z)) / (2 * (Real.sin (2 * π / m) : ℂ))) := by
    refine (key.congr_left ?_).congr_right ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have h2pi : (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      have hpi0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have hτ : 0 < (I * z / (2 * π)).im := by
        rw [h2pi, div_ofReal_im, I_mul_im]; exact div_pos hz.1 (by positivity)
      have hF := Fan_neg_eq H m hm hev _ hτ
      have hq : cexp (2 * π * I * (I * z / (2 * π))) = cexp (-z) := by
        congr 1; field_simp; ring_nf; rw [I_sq]; ring
      rw [hq] at hF
      have h1 : cexp (-z) ^ m = cexp (-(((m : ℝ) : ℂ) * z)) := by
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      have h2 : cexp (-z) ^ (2 * m) = cexp (-(((2 * m : ℝ)) * z)) := by
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      have h3 : cexp (-(π * I * (I * z / (2 * π)))) = cexp (z / 2) := by
        congr 1; field_simp; ring_nf; rw [I_sq]; ring
      have h4 : theta (2 * (I * z / (2 * π))) (2 * m * (I * z / (2 * π))) =
          theta (((1 / m : ℝ) : ℂ) * I * (((m / π : ℝ) : ℂ) * z))
            (I * (((m / π : ℝ) : ℂ) * z)) := by
        congr 1 <;> (push_cast; field_simp)
      have h5 : theta (2 * (I * z / (2 * π))) (m * (I * z / (2 * π))) =
          theta (((2 / m : ℝ) : ℂ) * I * (((m / (2 * π) : ℝ) : ℂ) * z))
            (I * (((m / (2 * π) : ℝ) : ℂ) * z)) := by
        congr 1 <;> (push_cast; field_simp)
      have h6 : theta (I * z / (2 * π)) (m * (I * z / (2 * π))) =
          theta (((1 / m : ℝ) : ℂ) * I * (((m / (2 * π) : ℝ) : ℂ) * z))
            (I * (((m / (2 * π) : ℝ) : ℂ) * z)) := by
        congr 1 <;> (push_cast; field_simp)
      rw [h1, h2, h3, h4, h5, h6] at hF
      simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply]
      rw [hF]
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply]
      have hs1 : (Real.sin (π * (1 / m)) : ℂ) ≠ 0 := by
        refine ofReal_ne_zero.2 (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
        rw [mul_one_div, div_lt_iff₀ hm0]; nlinarith
      have hs2 : (Real.sin (π * (2 / m)) : ℂ) ≠ 0 := by
        refine ofReal_ne_zero.2 (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
        rw [← mul_div_assoc, div_lt_iff₀ hm0]; nlinarith
      rw [lemma_4_2_alg z hz.1 m hm0 _ _ hs1 hs2, show π * (2 / (m : ℝ)) = 2 * π / m by ring,
        ofReal_natCast]
  refine (hF.pow ℓ).congr_right (Eventually.of_forall fun z => ?_)
  simp only [Pi.pow_apply]
  rw [div_pow, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- Asymptotic equivalence of real functions follows from that of their complex casts. -/
private lemma isEquivalent_of_ofReal {α : Type*} {l : Filter α} {u v : α → ℝ}
    (h : (fun x => (u x : ℂ)) ~[l] (fun x => (v x : ℂ))) : u ~[l] v := by
  unfold IsEquivalent at *
  rw [← isLittleO_norm_norm] at h ⊢
  convert h using 2 <;> simp [← ofReal_sub, Complex.norm_real]

/-- The positive reals tend to `0` inside every cone. -/
private lemma tendsto_ofReal_cone (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝[cone Δ] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
      continuous_ofReal.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨by simpa using ht, by simpa using mul_nonneg hΔ (le_of_lt ht)⟩

/-- **Theorem 1.3.** -/
theorem theorem_1_3 (H : ExternalResults) (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (hℓ : 0 < ℓ) :
    (fun n : ℕ => (coeffC m ℓ n : ℝ)) ~[atTop] (fun n : ℕ =>
      (ℓ : ℝ) ^ (1 / 4 : ℝ) /
          (2 ^ ((ℓ : ℝ) + 5 / 4) * (m : ℝ) ^ (1 / 4 : ℝ) * Real.sin (2 * π / m) ^ ℓ) *
        (-1) ^ n * Real.exp (π * Real.sqrt (2 * ℓ * n / m)) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  have hl0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  set s := Real.sin (2 * π / m) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by rw [div_lt_iff₀ hm0]; nlinarith)
  set b : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * (coeffC m ℓ n : ℝ) with hb
  set ν : ℝ := 1 / (2 ^ ℓ * s ^ ℓ) with hν
  set γ : ℝ := π ^ 2 * ℓ / (2 * m) with hγ
  have hν0 : 0 < ν := by positivity
  have hγ0 : 0 < γ := by positivity
  have hsum : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => (b n : ℂ) * q ^ n) (Fan m (-q) ^ ℓ) := by
    intro q hq
    have := hasSum_coeffC m ℓ (by omega) (-q) (by simpa using hq)
    convert this using 1
    funext n
    simp only [hb]
    push_cast
    rw [neg_pow q n]
    ring
  have hcplx : ∀ z : ℂ, 0 < z.re →
      ∑' n : ℕ, (b n : ℂ) * cexp (-(z * n)) = Fan m (-cexp (-z)) ^ ℓ := by
    intro z hz
    have hq : ‖cexp (-z)‖ < 1 := by
      rw [norm_exp, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by simpa using hz)
    rw [← (hsum _ hq).tsum_eq]
    congr 1
    funext n
    rw [← Complex.exp_nat_mul]
    congr 2
    ring
  have hreal : ∀ t : ℝ, 0 < t →
      ((∑' n : ℕ, b n * Real.exp (-(t * n)) : ℝ) : ℂ) =
        Fan m (-cexp (-(t : ℂ))) ^ ℓ := by
    intro t ht
    rw [ofReal_tsum, ← hcplx t (by simpa using ht)]
    congr 1
    funext n
    push_cast
    ring_nf
  have hmain := H.ingham b ν 0 γ hν0 hγ0 (fun n => lemma_4_1_nonneg m ℓ n hm hev)
    (lemma_4_1_mono m ℓ hm hev hℓ) (fun q hq => (hsum q hq).summable) ?_ ?_
  · have h2 := (IsEquivalent.refl (u := fun n : ℕ => (-1 : ℝ) ^ n)).mul hmain
    refine (h2.congr_left (Eventually.of_forall fun n => ?_)).congr_right
      ((eventually_ge_atTop 1).mono fun n hn => ?_)
    · simp only [Pi.mul_apply, hb]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    · simp only [Pi.mul_apply]
      have hn : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : (0 : ℝ) / 2 + 1 / 4 = 1 / 4 := by norm_num
      have e2 : (0 : ℝ) / 2 + 3 / 4 = 3 / 4 := by norm_num
      rw [e1, e2]
      have hγ4 : γ ^ (1 / 4 : ℝ) =
          π ^ (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 / 4 : ℝ) /
            (2 ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 4 : ℝ)) := by
        rw [hγ, Real.div_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hm0.le,
          ← Real.rpow_natCast π 2, ← Real.rpow_mul hpi.le]
        norm_num
      have hsq : √π = π ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow π
      have h2 : (2 : ℝ) ^ ((ℓ : ℝ) + 5 / 4) = 2 ^ ℓ * 2 * 2 ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_add two_pos, Real.rpow_natCast, show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
          Real.rpow_add two_pos, Real.rpow_one]
        ring
      have hex : 2 * √(γ * n) = π * √(2 * ℓ * n / m) := by
        have : γ * n = (π / 2) ^ 2 * (2 * ℓ * n / m) := by rw [hγ]; field_simp
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring
      rw [hγ4, hsq, h2, hex, hν]
      have : 0 < π ^ (1 / 2 : ℝ) := by positivity
      have : 0 < (n : ℝ) ^ (3 / 4 : ℝ) := by positivity
      field_simp
  · -- the real asymptotic, from Lemma 4.2 with `Δ = 0`
    have L := (lemma_4_2 H m ℓ hm hev 0 le_rfl).comp_tendsto (tendsto_ofReal_cone 0 le_rfl)
    refine isEquivalent_of_ofReal ((L.congr_left ?_).congr_right ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hreal t ht).symm
    · refine Eventually.of_forall fun t => ?_
      simp only [Function.comp_apply, Real.rpow_zero, mul_one, ← hs]
      rw [ofReal_mul, ofReal_exp, div_eq_inv_mul]
      congr 1
      · rw [hν]; push_cast; ring
      · congr 1
        rw [hγ]
        simp only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_natCast, ofReal_ofNat]
        ring
  · -- the bound in every cone, from Lemma 4.2
    intro Δ hΔ
    have L := (lemma_4_2 H m ℓ hm hev Δ hΔ).isBigO
    simp only [← hs] at L
    have L' := L.congr' (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hcplx z hz.1).symm) EventuallyEq.rfl
    refine L'.trans (IsBigO.of_bound ν ?_)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (by rintro rfl; simp [cone] at hz)
    have hre : (π ^ 2 * ℓ / (2 * m * z) : ℂ).re = γ * z.re / ‖z‖ ^ 2 := by
      rw [show (π ^ 2 * ℓ / (2 * m * z) : ℂ) = (γ : ℂ) / z by rw [hγ]; push_cast; ring,
        div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero, normSq_eq_norm_sq,
        mul_div_assoc]
    have hle : γ * z.re / ‖z‖ ^ 2 ≤ γ / ‖z‖ := by
      rw [div_le_div_iff₀ (by positivity) hz0]
      nlinarith [mul_le_mul_of_nonneg_left (re_le_norm z) (mul_nonneg hγ0.le hz0.le)]
    rw [norm_div, norm_exp, hre, Real.rpow_zero, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hs0.le, hν, one_div, div_eq_inv_mul]
    norm_num
    gcongr

/-- **Corollary 1.4.** For even `m ≥ 4`, `𝓁 ≥ 1` and all `n`, `sgn c^{[𝓁]}_m(n) = (-1)ⁿ`. -/
theorem corollary_1_4 (m ℓ : ℕ) (hm : 4 ≤ m) (hev : Even m) (hℓ : 0 < ℓ) (n : ℕ) :
    Real.sign (coeffC m ℓ n : ℝ) = (-1) ^ n := by
  have h := lemma_4_1_mono m ℓ hm hev hℓ (Nat.zero_le n)
  simp only [pow_zero, one_mul, coeffC_zero m ℓ (by omega), Int.cast_one] at h
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at h ⊢
    rw [Real.sign_of_pos (by linarith)]
  · rw [ho.neg_one_pow] at h ⊢
    rw [Real.sign_of_neg (by linarith)]

end ThetaSignPatterns
