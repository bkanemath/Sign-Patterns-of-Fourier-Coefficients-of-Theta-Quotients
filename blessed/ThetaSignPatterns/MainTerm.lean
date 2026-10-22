import ThetaSignPatterns.External

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# From the dominant terms of the exact formula to closed asymptotics
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- `√(8πΛ(n+δ)) - √(8πΛn) → 0`. -/
lemma sqrt_shift_sub_tendsto (Λ δ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (fun n : ℕ => Real.sqrt (8 * π * Λ * (n + δ)) - Real.sqrt (8 * π * Λ * n))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.sqrt (8 * π * Λ * n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  have hst : Tendsto (fun n : ℕ => Real.sqrt (8 * π * Λ * (n + δ)) + Real.sqrt (8 * π * Λ * n))
      atTop atTop := tendsto_atTop_mono (fun n => le_add_of_nonneg_left (Real.sqrt_nonneg _)) ht
  have h0 : Tendsto (fun n : ℕ => (8 * π * Λ * δ) /
      (Real.sqrt (8 * π * Λ * (n + δ)) + Real.sqrt (8 * π * Λ * n))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hst
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈-δ⌉₊] with n hn hnd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnd' : 0 ≤ (n : ℝ) + δ := by
    have := Nat.le_of_ceil_le hnd
    linarith
  have h1 : 0 < Real.sqrt (8 * π * Λ * n) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 ≤ Real.sqrt (8 * π * Λ * (n + δ)) := Real.sqrt_nonneg _
  have e1 := Real.sq_sqrt (show 0 ≤ 8 * π * Λ * (n + δ) by positivity)
  have e2 := Real.sq_sqrt (show 0 ≤ 8 * π * Λ * n by positivity)
  rw [div_eq_iff (by positivity)]
  nlinarith [e1, e2]

/-- `√(2πΛ/y) e^{s}/√(2πs) = C e^{s} s^{-3/2}` with `s = √(8πΛy)`, `C = 4πΛ/√(2π)`. -/
lemma bessel_closed_form (Λ y : ℝ) (hΛ : 0 < Λ) (hy : 0 < y) :
    Real.sqrt (2 * π * Λ / y) * (Real.exp (Real.sqrt (8 * π * Λ * y)) /
      Real.sqrt (2 * π * Real.sqrt (8 * π * Λ * y))) =
    4 * π * Λ / Real.sqrt (2 * π) * (Real.exp (Real.sqrt (8 * π * Λ * y)) *
      Real.sqrt (8 * π * Λ * y) ^ (-(3 / 2 : ℝ))) := by
  set s := Real.sqrt (8 * π * Λ * y) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 8 * π * Λ * y := Real.sq_sqrt (by positivity)
  have h1 : Real.sqrt (2 * π * Λ / y) = 4 * π * Λ / s := by
    rw [show 2 * π * Λ / y = (4 * π * Λ / s) ^ 2 by
      rw [div_pow, hs2]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have h2 : Real.sqrt (2 * π * s) = Real.sqrt (2 * π) * Real.sqrt s :=
    Real.sqrt_mul (by positivity) s
  have h3 : s ^ (-(3 / 2 : ℝ)) = (s * Real.sqrt s)⁻¹ := by
    rw [Real.rpow_neg hs0.le, Real.sqrt_eq_rpow,
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs0, Real.rpow_one]
  have hpi : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  rw [h1, h2, h3]
  field_simp

/-- `C (√(8πΛn))^{-3/2} = (Λ/(8π))^{1/4} n^{-3/4}`. -/
lemma bessel_const (Λ x : ℝ) (hΛ : 0 < Λ) (hx : 0 < x) :
    4 * π * Λ / Real.sqrt (2 * π) * Real.sqrt (8 * π * Λ * x) ^ (-(3 / 2 : ℝ)) =
      (Λ / (8 * π)) ^ (1 / 4 : ℝ) * x ^ (-(3 / 4 : ℝ)) := by
  have hA : 0 < 8 * π * Λ := by positivity
  rw [Real.sqrt_eq_rpow (8 * π * Λ * x), ← Real.rpow_mul (by positivity),
    Real.mul_rpow hA.le hx.le,
    show (1 / 2 : ℝ) * (-(3 / 2)) = -(3 / 4) by norm_num, ← mul_assoc]
  congr 1
  have hpi : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  rw [← pow_left_inj₀ (by positivity) (by positivity) (show (4 : ℕ) ≠ 0 by norm_num)]
  rw [mul_pow, ← Real.rpow_natCast ((Λ / (8 * π)) ^ (1 / 4 : ℝ)),
    ← Real.rpow_natCast ((8 * π * Λ) ^ (-(3 / 4 : ℝ))),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  rw [show (-(3 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
    show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one,
    Real.rpow_neg hA.le, Real.rpow_natCast,
    div_pow, show Real.sqrt (2 * π) ^ 4 = (Real.sqrt (2 * π) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- `√(2πΛ/(n+δ)) I₁(√(8πΛ(n+δ))) ∼ (Λ/(8π))^{1/4} n^{-3/4} e^{√(8πΛn)}` (uses E4). -/
theorem bessel_main (H : ExternalResults) (Λ δ : ℝ) (hΛ : 0 < Λ) :
    (fun n : ℕ => Real.sqrt (2 * π * Λ / (n + δ)) * besselI1 (Real.sqrt (8 * π * Λ * (n + δ))))
      ~[atTop] (fun n : ℕ => (Λ / (8 * π)) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(3 / 4 : ℝ)) *
        Real.exp (Real.sqrt (8 * π * Λ * n))) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (8 * π * Λ * (n + δ)) with hs_def
  set t : ℕ → ℝ := fun n => Real.sqrt (8 * π * Λ * n) with ht_def
  have hA : 0 < 8 * π * Λ := by positivity
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hA)
  have hs : Tendsto s atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_atTop_add_const_right _ δ tendsto_natCast_atTop_atTop).const_mul_atTop hA)
  have h1 : (fun n => besselI1 (s n)) ~[atTop]
      (fun n => Real.exp (s n) / Real.sqrt (2 * π * s n)) :=
    H.besselI1Asymp.comp_tendsto hs
  have h2 := (IsEquivalent.refl (u := fun n : ℕ => Real.sqrt (2 * π * Λ / (n + δ)))).mul h1
  have hdiff : Tendsto (fun n => s n - t n) atTop (𝓝 0) := sqrt_shift_sub_tendsto Λ δ hΛ
  have hexp : (fun n => Real.exp (s n)) ~[atTop] (fun n => Real.exp (t n)) := by
    apply isEquivalent_of_tendsto_one
    have : Tendsto (fun n => Real.exp (s n - t n)) atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp hdiff
      rw [Real.exp_zero] at this
      exact this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp [Real.exp_sub]
  have hst : s ~[atTop] t := by
    apply isEquivalent_of_tendsto_one
    have : Tendsto (fun n => 1 + (s n - t n) / t n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hdiff.div_atTop ht)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < t n := Real.sqrt_pos.2 (by positivity)
    simp only [Pi.div_apply]
    field_simp
    ring
  have hpow : (fun n => s n ^ (-(3 / 2 : ℝ))) ~[atTop] (fun n => t n ^ (-(3 / 2 : ℝ))) :=
    hst.rpow (fun n => Real.sqrt_nonneg _)
  have h3 := (IsEquivalent.refl (u := fun _ : ℕ => 4 * π * Λ / Real.sqrt (2 * π))).mul
    (hexp.mul hpow)
  refine (h2.trans ((h3.congr_left ?_).congr_right ?_)).congr_left ?_
  · filter_upwards [eventually_gt_atTop ⌈-δ⌉₊] with n hn
    have hy : 0 < (n : ℝ) + δ := by
      have := Nat.lt_of_ceil_lt hn
      linarith
    simp only [Pi.mul_apply]
    exact (bessel_closed_form Λ _ hΛ hy).symm
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.mul_apply, ht_def]
    rw [← bessel_const Λ n hΛ hn']
    ring
  · exact Eventually.of_forall fun n => rfl

/-- `(2Λ/π)^{1/4} = 2 (Λ/(8π))^{1/4}`. -/
lemma two_pow_quarter (Λ : ℝ) (hΛ : 0 < Λ) :
    (2 * Λ / π) ^ (1 / 4 : ℝ) = 2 * (Λ / (8 * π)) ^ (1 / 4 : ℝ) := by
  have h16 : (2 * Λ / π) = 2 ^ (4 : ℝ) * (Λ / (8 * π)) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    ring
  rw [h16, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `|e^{-2πinh/k}| = 1`. -/
lemma norm_cexp_phase (n : ℕ) (h : ℤ) (k : ℕ) :
    ‖cexp (-(2 * π * I * n * h / k))‖ = 1 := by
  rw [show -(2 * π * I * n * h / k) = ((-(2 * π * n * h / k) : ℝ) : ℂ) * I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Two conjugate dominant cusps `h₁/k`, `h₂/k` (`h₁ + h₂ = k`). -/
theorem two_cusp (H : ExternalResults) (Λ δ : ℝ) (hΛ : 0 < Λ) (h₁ h₂ : ℤ) (k : ℕ) (hk : 0 < k)
    (hsum : h₁ + h₂ = k) (B : ℂ) (a : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hu : ∀ n : ℕ, κ ≤ |(B * cexp (-(2 * π * I * n * h₁ / k))).re|)
    (ho : (fun n : ℕ => (a n : ℂ) -
        (rzTerm Λ δ (h₁, k) (cexp (2 * π * I * δ * h₁ / k) * B) n +
          rzTerm Λ δ (h₂, k) (cexp (2 * π * I * δ * h₂ / k) * starRingEnd ℂ B) n))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (Real.sqrt (8 * π * Λ * n)))) :
    (fun n : ℕ => a n) ~[atTop] (fun n : ℕ => (2 * Λ / π) ^ (1 / 4 : ℝ) *
      (B * cexp (-(2 * π * I * n * h₁ / k))).re * (n : ℝ) ^ (-(3 / 4 : ℝ)) *
        Real.exp (Real.sqrt (8 * π * Λ * n))) := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ,
      v = fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (Real.sqrt (8 * π * Λ * n)) := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → ℝ,
      u = fun n : ℕ => (B * cexp (-(2 * π * I * n * h₁ / k))).re := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun n : ℕ =>
      Real.sqrt (2 * π * Λ / (n + δ)) * besselI1 (Real.sqrt (8 * π * Λ * (n + δ))) := ⟨_, rfl⟩
  set c : ℝ := (Λ / (8 * π)) ^ (1 / 4 : ℝ) with hc
  set K : ℝ := (2 * Λ / π) ^ (1 / 4 : ℝ) with hK_def
  have hK : K = 2 * c := two_pow_quarter Λ hΛ
  have hKpos : 0 < K := by positivity
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsumC : (h₁ : ℂ) + h₂ = k := by exact_mod_cast hsum
  -- the two cusp terms are conjugate
  have hsum_eq : ∀ n : ℕ,
      rzTerm Λ δ (h₁, k) (cexp (2 * π * I * δ * h₁ / k) * B) n +
        rzTerm Λ δ (h₂, k) (cexp (2 * π * I * δ * h₂ / k) * starRingEnd ℂ B) n =
      ((2 * β n * u n : ℝ) : ℂ) := by
    intro n
    have e1 : cexp (2 * π * I * δ * h₁ / k) * cexp (-(2 * π * I * ((n : ℂ) + δ) * h₁ / k)) =
        cexp (-(2 * π * I * n * h₁ / k)) := by
      rw [← Complex.exp_add]; congr 1; field_simp; ring
    have e2 : cexp (2 * π * I * δ * h₂ / k) * cexp (-(2 * π * I * ((n : ℂ) + δ) * h₂ / k)) =
        starRingEnd ℂ (cexp (-(2 * π * I * n * h₁ / k))) := by
      rw [← Complex.exp_add, ← Complex.exp_conj]
      have hh₂ : (h₂ : ℂ) = k - h₁ := by rw [← hsumC]; ring
      have hc' : starRingEnd ℂ (-(2 * π * I * n * h₁ / k)) = 2 * π * I * n * h₁ / k := by
        simp [map_neg, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
        ring
      rw [hc', show 2 * π * I * δ * h₂ / k + -(2 * π * I * ((n : ℂ) + δ) * h₂ / k) =
          2 * π * I * n * h₁ / k + ((-(n : ℤ) : ℤ) : ℂ) * (2 * π * I) by
        rw [hh₂]; push_cast; field_simp; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have : rzTerm Λ δ (h₁, k) (cexp (2 * π * I * δ * h₁ / k) * B) n +
        rzTerm Λ δ (h₂, k) (cexp (2 * π * I * δ * h₂ / k) * starRingEnd ℂ B) n =
        ((β n : ℝ) : ℂ) *
          (B * (cexp (2 * π * I * δ * h₁ / k) * cexp (-(2 * π * I * ((n : ℂ) + δ) * h₁ / k))) +
           starRingEnd ℂ B * (cexp (2 * π * I * δ * h₂ / k) *
             cexp (-(2 * π * I * ((n : ℂ) + δ) * h₂ / k)))) := by
      simp only [rzTerm, hβ]
      push_cast
      ring
    rw [this, e1, e2, ← map_mul, Complex.add_conj, hu_def]
    push_cast
    ring
  -- the real error term
  have ho' : (fun n => a n - 2 * β n * u n) =o[atTop] v := by
    refine IsLittleO.of_norm_left ?_
    have e : (fun n => ‖a n - 2 * β n * u n‖) = fun n => ‖(a n : ℂ) -
        (rzTerm Λ δ (h₁, k) (cexp (2 * π * I * δ * h₁ / k) * B) n +
          rzTerm Λ δ (h₂, k) (cexp (2 * π * I * δ * h₂ / k) * starRingEnd ℂ B) n)‖ := by
      funext n
      rw [hsum_eq n, ← Complex.ofReal_sub, Complex.norm_real]
    rw [e, hv]
    exact ho.norm_left
  -- Bessel main term
  have hb : β ~[atTop] (fun n => c * v n) := by
    rw [hβ, hv]
    convert bessel_main H Λ δ hΛ using 1
    funext n
    ring
  have hb' : (fun n => β n - c * v n) =o[atTop] v :=
    hb.isLittleO.trans_isBigO (isBigO_const_mul_self c v atTop)
  have hu_bd : u =O[atTop] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun n => ?_)
    rw [hu_def, norm_one, mul_one, Real.norm_eq_abs]
    calc |(B * cexp (-(2 * π * I * n * h₁ / k))).re| ≤ ‖B * cexp (-(2 * π * I * n * h₁ / k))‖ :=
          Complex.abs_re_le_norm _
      _ = ‖B‖ := by rw [norm_mul, norm_cexp_phase, mul_one]
  set T : ℕ → ℝ := fun n => K * (B * cexp (-(2 * π * I * n * h₁ / k))).re *
    (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (Real.sqrt (8 * π * Λ * n)) with hT
  have h2 : (fun n => 2 * β n * u n - T n) =o[atTop] v := by
    have := (hu_bd.mul_isLittleO hb').const_mul_left 2
    refine (this.congr_left fun n => ?_).congr_right fun n => ?_
    · simp only [hT, hK, hu_def, hv]; ring
    · simp
  have h3 : (fun n => a n - T n) =o[atTop] v :=
    (ho'.add h2).congr_left fun n => by ring
  have h4 : v =O[atTop] T := by
    refine IsBigO.of_bound (1 / (K * κ)) (Eventually.of_forall fun n => ?_)
    have hT' : T n = K * u n * v n := by simp only [hT, hu_def, hv]; ring
    rw [hT', Real.norm_eq_abs, Real.norm_eq_abs]
    have hun : κ ≤ |u n| := by rw [hu_def]; exact hu n
    have : K * κ * |v n| ≤ |K * u n * v n| := by
      rw [abs_mul, abs_mul, abs_of_pos hKpos]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hun hKpos.le) (abs_nonneg _)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith
  exact h3.trans_isBigO h4

/-- Asymptotically equivalent sequences eventually have the same sign. -/
theorem sign_eventually_of_equiv (a v : ℕ → ℝ) (h : a ~[atTop] v)
    (hv : ∀ᶠ n in atTop, v n ≠ 0) : ∀ᶠ n in atTop, Real.sign (a n) = Real.sign (v n) := by
  have ht := (isEquivalent_iff_tendsto_one hv).1 h
  have hpos : ∀ᶠ n in atTop, 0 < (a / v) n := ht.eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos, hv] with n hp hvn
  simp only [Pi.div_apply] at hp
  rcases lt_or_gt_of_ne hvn with hneg | hpos'
  · have : a n < 0 := by
      by_contra hc; rw [not_lt] at hc
      have := div_nonpos_of_nonneg_of_nonpos hc hneg.le; linarith
    rw [Real.sign_of_neg this, Real.sign_of_neg hneg]
  · have : 0 < a n := by
      by_contra hc; rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc hpos'.le; linarith
    rw [Real.sign_of_pos this, Real.sign_of_pos hpos']

end ThetaSignPatterns
