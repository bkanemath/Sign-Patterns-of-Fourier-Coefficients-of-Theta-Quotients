import ThetaSignPatterns.ThetaBasic
import ThetaSignPatterns.ThetaProduct

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Growth at every cusp (Lemmas 3.1 and 5.1)
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- If `f ∼ g` and `‖g‖ e ≡ C > 0`, then `‖f‖ e` is eventually between two positive constants. -/
private lemma norm_bounds_of_equiv {f g : ℝ → ℂ} {e : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hfg : f ~[atTop] g) (hg : ∀ᶠ y in atTop, ‖g y‖ * e y = C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ y in atTop, c₁ ≤ ‖f y‖ * e y ∧ ‖f y‖ * e y ≤ c₂ := by
  have hg0 : ∀ᶠ y in atTop, g y ≠ 0 := hg.mono fun y hy h0 => by
    rw [h0, norm_zero, zero_mul] at hy; exact hC.ne hy
  have ht : Tendsto (fun y => ‖f y / g y‖) atTop (𝓝 1) := by
    have := ((isEquivalent_iff_tendsto_one hg0).1 hfg).norm
    simpa using this
  have h1 : ∀ᶠ y in atTop, ‖f y / g y‖ ∈ Set.Ioo (1 / 2 : ℝ) 2 :=
    ht (Ioo_mem_nhds (by norm_num) (by norm_num))
  refine ⟨C / 2, 2 * C, by positivity, by positivity, ?_⟩
  filter_upwards [h1, hg, hg0] with y hy hgy hg0y
  have hn : ‖g y‖ ≠ 0 := norm_ne_zero_iff.2 hg0y
  have : ‖f y‖ * e y = ‖f y / g y‖ * C := by
    rw [← hgy, norm_div]; field_simp
  rw [this]
  constructor <;> nlinarith [hy.1, hy.2]

/-- Reduction of `theta_vertical` to `0 ≤ a < 1` via `theta_quasi`. -/
private lemma theta_vertical_red (a b x₀ y : ℝ) (hy : 0 < y) :
    ‖theta (a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
        Real.exp (-(π * y * (a ^ 2 + gfr a - 1 / 4))) =
      ‖theta (Int.fract a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
        Real.exp (-(π * y * (Int.fract a - 1 / 4))) := by
  have ha : a = (⌊a⌋ : ℝ) + Int.fract a := (Int.floor_add_fract a).symm
  have hτ : 0 < (x₀ + I * y : ℂ).im := by simpa using hy
  have hq := theta_quasi ⌊a⌋ 0 (Int.fract a * (x₀ + I * y) + b) (x₀ + I * y) hτ
  have hw : ((Int.fract a : ℝ) * (x₀ + I * y) + b : ℂ) + (⌊a⌋ : ℤ) * (x₀ + I * y) + ((0 : ℤ) : ℂ) =
      a * (x₀ + I * y) + b := by
    conv_rhs => rw [ha]
    push_cast; ring
  rw [hw] at hq
  rw [hq, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, norm_zpow, norm_neg,
    norm_one, one_zpow, one_mul]
  have e1 : (-(π * I * ((⌊a⌋ : ℤ) : ℂ) ^ 2 * (x₀ + I * y))).re = π * (⌊a⌋ : ℝ) ^ 2 * y := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have e2 : (-(2 * π * I * ((⌊a⌋ : ℤ) : ℂ) * ((Int.fract a : ℝ) * (x₀ + I * y) + b))).re =
      2 * π * (⌊a⌋ : ℝ) * Int.fract a * y := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [e1, e2, mul_comm (Real.exp _ * Real.exp _), mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  unfold gfr
  linear_combination (-(π * y) * (a + ⌊a⌋ + Int.fract a)) * ha

/-- `|ϑ(aτ+b;τ)| ≍ e^{πy(a² + 𝔤(a) - 1/4)}` along `τ = x₀ + iy`, `y → ∞`
(if `a ∈ ℤ` we need `b ∉ ℤ`). -/
theorem theta_vertical (H : ExternalResults) (a b x₀ : ℝ)
    (hab : (∃ n : ℤ, a = n) → ∀ n : ℤ, b ≠ n) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ y : ℝ in atTop,
      c₁ ≤ ‖theta (a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
          Real.exp (-(π * y * (a ^ 2 + gfr a - 1 / 4))) ∧
      ‖theta (a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
          Real.exp (-(π * y * (a ^ 2 + gfr a - 1 / 4))) ≤ c₂ := by
  suffices hs : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ y : ℝ in atTop,
      c₁ ≤ ‖theta (Int.fract a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
          Real.exp (-(π * y * (Int.fract a - 1 / 4))) ∧
      ‖theta (Int.fract a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
          Real.exp (-(π * y * (Int.fract a - 1 / 4))) ≤ c₂ by
    obtain ⟨c₁, c₂, h₁, h₂, hev⟩ := hs
    refine ⟨c₁, c₂, h₁, h₂, ?_⟩
    filter_upwards [hev, eventually_gt_atTop 0] with y hy hy0
    rw [theta_vertical_red a b x₀ y hy0]
    exact hy
  rcases (Int.fract_nonneg a).eq_or_lt with h0 | hpos
  · -- `a ∈ ℤ`: E3.2
    have hb : ∀ n : ℤ, b ≠ n := hab ⟨⌊a⌋, by
      have := Int.floor_add_fract a
      rw [← h0, add_zero] at this
      exact this.symm⟩
    have hsin : Real.sin (π * b) ≠ 0 := by
      intro hs
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
      exact hb n (by
        have := Real.pi_pos
        field_simp at hn
        linarith [hn])
    have hfg := H.thetaAsymp2 b x₀ hb
    have key := norm_bounds_of_equiv (e := fun y : ℝ => Real.exp (-(π * y * (0 - 1 / 4))))
      (C := 2 * |Real.sin (π * b)|) (by positivity) hfg (Eventually.of_forall fun y => by
        have e1 : (π * I * (x₀ + I * y) / 4 : ℂ).re = -(π * y / 4) := by
          simp [Complex.mul_re, Complex.mul_im]
          ring
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, e1,
          mul_assoc, ← Real.exp_add]
        have : -(π * y / 4) + -(π * y * (0 - 1 / 4)) = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
        norm_num)
    obtain ⟨c₁, c₂, h₁, h₂, hev⟩ := key
    refine ⟨c₁, c₂, h₁, h₂, ?_⟩
    filter_upwards [hev] with y hy
    rw [← h0]
    simp only [Complex.ofReal_zero, zero_mul, zero_add]
    exact hy
  · -- `0 < {a} < 1`: E3.1
    have hfg := H.thetaAsymp1 (Int.fract a) b x₀ hpos (Int.fract_lt_one a)
    exact norm_bounds_of_equiv one_pos hfg (Eventually.of_forall fun y => by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_exp,
        Complex.norm_exp]
      have e1 : (-(π * I * (b : ℂ))).re = 0 := by simp
      have e2 : (2 * π * I * (x₀ + I * y) * (1 / 8 - ((Int.fract a : ℝ) : ℂ) / 2)).re =
          -(2 * π * y * (1 / 8 - Int.fract a / 2)) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [e1, e2, Real.exp_zero, one_mul, ← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring)

/-- `Re (r (p + iq)²) = r (p² - q²)`. -/
private lemma re_mul_sq (r p q : ℝ) : ((r : ℂ) * ((p : ℂ) + I * q) ^ 2).re = r * (p ^ 2 - q ^ 2) := by
  simp [sq, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 800000 in
/-- Lemma 3.1 with `m = dμ`, `k = dκ`, `gcd(μ,κ) = 1`. -/
private lemma Gm_cusp_core (H : ExternalResults) (d μ κ : ℕ) (hm : 3 ≤ d * μ) (hodd : Odd (d * μ))
    (h : ℤ) (hk : 0 < d * κ) (hcop : Int.gcd h ((d * κ : ℕ) : ℤ) = 1) (hdpos : 0 < d)
    (hcopμκ : Nat.Coprime μ κ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ z : ℝ in 𝓝[>] 0,
      c₁ * Real.exp (π / ((μ : ℝ) * κ) * (gfr ((h : ℝ) / d) - gfr (2 * ((h : ℝ) / d))) / z) ≤
        ‖Gm (d * μ) ((h + I * z) / ((d * κ : ℕ) : ℂ))‖ ∧
      ‖Gm (d * μ) ((h + I * z) / ((d * κ : ℕ) : ℂ))‖ ≤
        c₂ * Real.exp (π / ((μ : ℝ) * κ) * (gfr ((h : ℝ) / d) - gfr (2 * ((h : ℝ) / d))) / z) := by
  have hμpos : 0 < μ := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hκpos : 0 < κ := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  -- coprimality: `gcd(μh, κ) = 1`
  have hcopZ : IsCoprime h ((d * κ : ℕ) : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 hcop
  have hcopκ : IsCoprime h (κ : ℤ) :=
    hcopZ.of_isCoprime_of_dvd_right (by push_cast; exact dvd_mul_left _ _)
  have hcopd : IsCoprime (d : ℤ) h :=
    (hcopZ.of_isCoprime_of_dvd_right (by push_cast; exact dvd_mul_right _ _)).symm
  have hHK : Int.gcd ((μ : ℤ) * h) κ = 1 :=
    Int.isCoprime_iff_gcd_eq_one.1 ((Nat.isCoprime_iff_coprime.2 hcopμκ).mul_left hcopκ)
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 hHK
  obtain ⟨t, ht⟩ : (κ : ℤ) ∣ ((μ : ℤ) * h) * (-u) + 1 := ⟨v, by linear_combination (-1 : ℤ) * huv⟩
  have hdvd : (κ : ℤ) ∣ ((μ : ℤ) * h) * (-u) + 1 := ⟨t, ht⟩
  set H' : ℤ := -u with hH'
  set a : ℝ := (h : ℝ) / d with ha
  set b : ℝ := -(t : ℝ) / (d * μ) with hb
  set x₀ : ℝ := (H' : ℝ) / κ with hx₀
  -- the side conditions force `d = 1`
  have hd1 : ((∃ n : ℤ, a = n) ∨ (∃ n : ℤ, 2 * a = n)) → d = 1 := by
    intro hn
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hdvd2 : (d : ℤ) ∣ 2 * h := by
      rcases hn with ⟨n, hn⟩ | ⟨n, hn⟩
      · have h1 : (h : ℝ) = n * d := by rw [ha] at hn; field_simp at hn; linarith
        have h2 : h = n * d := by exact_mod_cast h1
        exact Dvd.dvd.mul_left ⟨n, by rw [h2]; ring⟩ 2
      · have h1 : (2 * h : ℝ) = n * d := by rw [ha] at hn; field_simp at hn; linarith
        have h2 : 2 * h = n * d := by exact_mod_cast h1
        exact ⟨n, by rw [h2]; ring⟩
    have h2 : (d : ℤ) ∣ 2 := hcopd.dvd_of_dvd_mul_right hdvd2
    have h2' : d ∣ 2 := by exact_mod_cast h2
    have hdodd : Odd d := (Nat.odd_mul.1 hodd).1
    have hle := Nat.le_of_dvd (by norm_num) h2'
    rcases hdodd with ⟨j, hj⟩
    omega
  have hbn : d = 1 → ∀ n : ℤ, b ≠ n ∧ 2 * b ≠ n := by
    rintro rfl n
    have hμodd : Odd μ := by simpa using hodd
    have hμ0 : (μ : ℝ) ≠ 0 := by positivity
    have key : ¬ (μ : ℤ) ∣ 2 * t := by
      intro hμt
      have hnd : ¬ 2 ∣ μ := by have := Nat.odd_iff.1 hμodd; omega
      have hcop2 : IsCoprime (μ : ℤ) ((2 : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.prime_two.coprime_iff_not_dvd.2 hnd).symm
      have h1 : (μ : ℤ) ∣ t := hcop2.dvd_of_dvd_mul_left (by exact_mod_cast hμt)
      have h2 : (μ : ℤ) ∣ 1 := by
        have : (1 : ℤ) = κ * t - μ * (h * H') := by linear_combination ht
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_right _ _)
      have h3 : μ ∣ 1 := by exact_mod_cast h2
      have := Nat.le_of_dvd one_pos h3
      omega
    constructor
    · intro hbn; apply key
      have h1 : (t : ℝ) = -(n * μ) := by rw [hb] at hbn; field_simp at hbn; push_cast at hbn; linarith
      have h2 : t = -(n * μ) := by exact_mod_cast h1
      exact ⟨-(2 * n), by rw [h2]; ring⟩
    · intro hbn; apply key
      have h1 : (2 * t : ℝ) = -(n * μ) := by
        rw [hb] at hbn; field_simp at hbn; push_cast at hbn; linarith
      have h2 : 2 * t = -(n * μ) := by exact_mod_cast h1
      exact ⟨-n, by rw [h2]; ring⟩
  -- the bounds along the vertical line `x₀ + iy`, `y = 1/(κμz) → ∞`
  have hyt : Tendsto (fun z : ℝ => 1 / ((κ : ℝ) * μ * z)) (𝓝[>] 0) atTop := by
    have : (fun z : ℝ => 1 / ((κ : ℝ) * μ * z)) = fun z => ((κ : ℝ) * μ)⁻¹ * z⁻¹ := by
      funext z; rw [one_div, mul_inv]
    rw [this]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  obtain ⟨c₁, c₂, hc₁, hc₂, hev1⟩ :=
    theta_vertical H a b x₀ (fun ha' n => (hbn (hd1 (Or.inl ha')) n).1)
  obtain ⟨d₁, d₂, hd₁, hd₂, hev2⟩ :=
    theta_vertical H (2 * a) (2 * b) x₀ (fun ha' n => (hbn (hd1 (Or.inr ha')) n).2)
  have hev1' := hyt.eventually hev1
  have hev2' := hyt.eventually hev2
  refine ⟨c₁ / d₂ * Real.exp (-(3 * π / (d * κ * (d * μ)))), c₂ / d₁, by positivity,
    by positivity, ?_⟩
  filter_upwards [hev1', hev2', self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with z hz1 hz2 hz0 hz01
  have hz0' : 0 < z := hz0
  set y : ℝ := 1 / ((κ : ℝ) * μ * z) with hy
  set A : ℝ := π / ((μ : ℝ) * κ) * (gfr a - gfr (2 * a)) with hA
  set P₁ := ‖theta (a * (x₀ + I * y) + b) (x₀ + I * y)‖ *
    Real.exp (-(π * y * (a ^ 2 + gfr a - 1 / 4))) with hP₁
  set P₂ := ‖theta ((2 * a : ℝ) * (x₀ + I * y) + (2 * b : ℝ)) (x₀ + I * y)‖ *
    Real.exp (-(π * y * ((2 * a) ^ 2 + gfr (2 * a) - 1 / 4))) with hP₂
  set W : ℝ := -(3 * π * z / (d * κ * (d * μ))) with hW
  -- the transformation E2.1 at `mτ = (μh + iμz)/κ`
  obtain ⟨c, hc0, hc⟩ := H.thetaCuspTransform ((μ : ℤ) * h) κ H' hκpos hHK hdvd ((μ : ℝ) * z)
    (by positivity)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκpos.ne'
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμpos.ne'
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz0'.ne'
  set τ : ℂ := (h + I * z) / ((d * κ : ℕ) : ℂ) with hτ
  have hmτ : ((d * μ : ℕ) : ℂ) * τ =
      ((((μ : ℤ) * h : ℤ) : ℂ) + I * (((μ : ℝ) * z : ℝ) : ℂ)) / (κ : ℂ) := by
    rw [hτ]; push_cast; field_simp
  have hτ₁ : ((H' : ℂ) + I / (((μ : ℝ) * z : ℝ) : ℂ)) / (κ : ℂ) = (x₀ : ℂ) + I * (y : ℂ) := by
    rw [hx₀, hy]; push_cast; field_simp
  have htC : (t : ℂ) = ((μ : ℂ) * h * H' + 1) / κ := by
    rw [eq_div_iff hκ0]; rw [hH']; exact_mod_cast (by linear_combination (-1 : ℤ) * ht : (t : ℤ) * κ = _)
  have hw1 : I * τ / (((μ : ℝ) * z : ℝ) : ℂ) = (a : ℂ) * ((x₀ : ℂ) + I * (y : ℂ)) + (b : ℂ) := by
    rw [hτ, ha, hx₀, hy, hb]; push_cast; rw [htC]; field_simp; ring_nf; rw [I_sq]; ring
  have hw2 : I * (2 * τ) / (((μ : ℝ) * z : ℝ) : ℂ) =
      ((2 * a : ℝ) : ℂ) * ((x₀ : ℂ) + I * (y : ℂ)) + ((2 * b : ℝ) : ℂ) := by
    rw [show I * (2 * τ) / (((μ : ℝ) * z : ℝ) : ℂ) = 2 * (I * τ / (((μ : ℝ) * z : ℝ) : ℂ)) by ring,
      hw1]
    push_cast; ring
  have hpq : τ = ((h / (d * κ) : ℝ) : ℂ) + I * ((z / (d * κ) : ℝ) : ℂ) := by
    rw [hτ]; push_cast; ring
  have hre1 : (-(π * (κ : ℂ) * τ ^ 2 / (((μ : ℝ) * z : ℝ) : ℂ))).re =
      -(π * κ / (μ * z)) * ((h / (d * κ)) ^ 2 - (z / (d * κ)) ^ 2) := by
    rw [← re_mul_sq, hpq]; congr 1; push_cast; ring
  have hre2 : (-(π * (κ : ℂ) * (2 * τ) ^ 2 / (((μ : ℝ) * z : ℝ) : ℂ))).re =
      -(4 * π * κ / (μ * z)) * ((h / (d * κ)) ^ 2 - (z / (d * κ)) ^ 2) := by
    rw [← re_mul_sq, hpq]; congr 1; push_cast; ring
  have hP₂pos : 0 < P₂ := lt_of_lt_of_le hd₁ hz2.1
  have hθ₂ : ‖theta ((2 * a : ℝ) * (x₀ + I * y) + (2 * b : ℝ)) (x₀ + I * y)‖ ≠ 0 := by
    intro h0; rw [hP₂, h0, zero_mul] at hP₂pos; exact lt_irrefl _ hP₂pos
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc0
  have hE : -(π * κ / (μ * z)) * ((h / (d * κ)) ^ 2 - (z / (d * κ)) ^ 2) =
      -(4 * π * κ / (μ * z)) * ((h / (d * κ)) ^ 2 - (z / (d * κ)) ^ 2) +
        -(π * y * (a ^ 2 + gfr a - 1 / 4)) - -(π * y * ((2 * a) ^ 2 + gfr (2 * a) - 1 / 4)) +
        W + A / z := by
    rw [hy, hW, hA, ha]
    field_simp
    ring
  have hid : ‖Gm (d * μ) τ‖ = P₁ / P₂ * Real.exp W * Real.exp (A / z) := by
    unfold Gm
    rw [hmτ, hc, hc, hτ₁, hw1, hw2, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Complex.norm_exp, Complex.norm_exp, hre1, hre2, hE, hP₁, hP₂]
    simp only [Real.exp_add, Real.exp_sub]
    field_simp
  rw [hid]
  clear_value P₁ P₂ W A y
  have hW1 : -(3 * π / (d * κ * (d * μ))) ≤ W := by
    rw [hW, neg_le_neg_iff]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [Real.pi_pos, hz01.2]
  have hW2 : W ≤ 0 := by rw [hW]; have := Real.pi_pos; apply neg_nonpos.2; positivity
  have hEA := Real.exp_pos (A / z)
  have hq1 : c₁ / d₂ ≤ P₁ / P₂ := by
    rw [div_le_div_iff₀ (by positivity) hP₂pos]
    nlinarith [mul_le_mul_of_nonneg_left hz2.2 hc₁.le, mul_le_mul_of_nonneg_right hz1.1 hd₂.le]
  have hq2 : P₁ / P₂ ≤ c₂ / d₁ := by
    rw [div_le_div_iff₀ hP₂pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hz1.2 hd₁.le, mul_le_mul_of_nonneg_left hz2.1 hc₂.le]
  have he1 : Real.exp (-(3 * π / (d * κ * (d * μ)))) ≤ Real.exp W := Real.exp_le_exp.2 hW1
  have he2 : Real.exp W ≤ 1 := Real.exp_le_one_iff.2 hW2
  have hq0 : 0 ≤ c₁ / d₂ := by positivity
  constructor
  · apply mul_le_mul_of_nonneg_right _ hEA.le
    exact mul_le_mul hq1 he1 (Real.exp_pos _).le (hq0.trans hq1)
  · apply mul_le_mul_of_nonneg_right _ hEA.le
    calc P₁ / P₂ * Real.exp W ≤ P₁ / P₂ * 1 :=
          mul_le_mul_of_nonneg_left he2 (hq0.trans hq1)
      _ ≤ c₂ / d₁ := by rw [mul_one]; exact hq2

/-- **Lemma 3.1.** `|G_m((h+iz)/k)| ≍ e^{A_m(h,k)/z}` as `z → 0⁺`, for odd `m ≥ 3`. -/
theorem Gm_cusp_growth (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) (h : ℤ)
    (k : ℕ) (hk : 0 < k) (hcop : Int.gcd h k = 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ z : ℝ in 𝓝[>] 0,
      c₁ * Real.exp (Acusp m h k / z) ≤ ‖Gm m ((h + I * z) / k)‖ ∧
      ‖Gm m ((h + I * z) / k)‖ ≤ c₂ * Real.exp (Acusp m h k / z) := by
  -- `d = gcd(m,k)`, `m = dμ`, `k = dκ`
  have hdpos : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left _ (by omega)
  have hmd : m = Nat.gcd m k * (m / Nat.gcd m k) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left m k)).symm
  have hkd : k = Nat.gcd m k * (k / Nat.gcd m k) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m k)).symm
  have hcopμκ : Nat.Coprime (m / Nat.gcd m k) (k / Nat.gcd m k) :=
    Nat.coprime_div_gcd_div_gcd hdpos
  have hA : Acusp m h k = π / (((m / Nat.gcd m k : ℕ) : ℝ) * ((k / Nat.gcd m k : ℕ) : ℝ)) *
      (gfr ((h : ℝ) / (Nat.gcd m k : ℝ)) - gfr (2 * ((h : ℝ) / (Nat.gcd m k : ℝ)))) := by
    rw [Acusp, mul_div_assoc]
  rw [hA]
  generalize Nat.gcd m k = d at hdpos hmd hkd hcopμκ ⊢
  generalize m / d = μ at hmd hkd hcopμκ ⊢
  generalize k / d = κ at hmd hkd hcopμκ ⊢
  subst hmd hkd
  exact Gm_cusp_core H d μ κ hm hodd h hk hcop hdpos hcopμκ

/-- `|e^{-3πiτ/m}| = e^{3πz/(km)}` at `τ = (h+iz)/k`. -/
private lemma norm_exp_ratio (m : ℕ) (h : ℤ) (k : ℕ) (z : ℝ) :
    ‖cexp (π * I * ((h + I * z) / k) / m) / cexp (4 * π * I * ((h + I * z) / k) / m)‖ =
      Real.exp (3 * π * z / (k * m)) := by
  rw [← Complex.exp_sub, Complex.norm_exp]
  congr 1
  have : (π * I * ((h + I * z) / k) / m - 4 * π * I * ((h + I * z) / k) / m : ℂ) =
      ((3 * π * z / (k * m) : ℝ) : ℂ) + ((-(3 * π * h / (k * m)) : ℝ) : ℂ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [this]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- `f_{m,𝓁} = (e^{-3πiτ/m} G_m)^𝓁`. -/
private lemma fMod_eq_Gm (m ℓ : ℕ) (τ : ℂ) :
    fMod m ℓ τ = (cexp (π * I * τ / m) / cexp (4 * π * I * τ / m) * Gm m τ) ^ ℓ := by
  unfold fMod Gm
  rw [mul_div_mul_comm]

/-- `f̃_{m,λ} = (e^{-3πiτ/m} G_m)^{-λ}`. -/
private lemma fModT_eq_Gm (m lam : ℕ) (τ : ℂ) :
    fModT m lam τ = (cexp (π * I * τ / m) / cexp (4 * π * I * τ / m) * Gm m τ)⁻¹ ^ lam := by
  unfold fModT Gm
  rw [mul_inv, inv_div, inv_div, mul_div_mul_comm]

/-- Lemma 3.1 for `f_{m,𝓁}`: `|f_{m,𝓁}((h+iz)/k)| = O(e^{𝓁 A_m(h,k)/z})`. -/
theorem fMod_cusp_bound (H : ExternalResults) (m ℓ : ℕ) (hm : 3 ≤ m) (hodd : Odd m) (h : ℤ)
    (k : ℕ) (hk : 0 < k) (hcop : Int.gcd h k = 1) :
    ∃ K : ℝ, ∀ᶠ z : ℝ in 𝓝[>] 0,
      ‖fMod m ℓ ((h + I * z) / k)‖ ≤ K * Real.exp (ℓ * Acusp m h k / z) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hev⟩ := Gm_cusp_growth H m hm hodd h k hk hcop
  refine ⟨(Real.exp (3 * π / (k * m)) * c₂) ^ ℓ, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with z hz hz01
  rw [fMod_eq_Gm, norm_pow, norm_mul, norm_exp_ratio, mul_div_assoc (ℓ : ℝ), Real.exp_nat_mul,
    ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hkm : (0 : ℝ) < k * m := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have h1 : Real.exp (3 * π * z / (k * m)) ≤ Real.exp (3 * π / (k * m)) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hkm.le
    nlinarith [Real.pi_pos, hz01.2]
  calc Real.exp (3 * π * z / (k * m)) * ‖Gm m ((h + I * z) / k)‖
      ≤ Real.exp (3 * π / (k * m)) * (c₂ * Real.exp (Acusp m h k / z)) :=
        mul_le_mul h1 hz.2 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- **Lemma 5.1.** `|f̃_{m,λ}((h+iz)/k)| = O(e^{-λ A_m(h,k)/z})`. -/
theorem fModT_cusp_bound (H : ExternalResults) (m lam : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (h : ℤ) (k : ℕ) (hk : 0 < k) (hcop : Int.gcd h k = 1) :
    ∃ K : ℝ, ∀ᶠ z : ℝ in 𝓝[>] 0,
      ‖fModT m lam ((h + I * z) / k)‖ ≤ K * Real.exp (-(lam * Acusp m h k) / z) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hev⟩ := Gm_cusp_growth H m hm hodd h k hk hcop
  refine ⟨c₁⁻¹ ^ lam, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
  have hz0' : 0 < z := hz0
  have hexp : Real.exp (-(lam * Acusp m h k) / z) = (Real.exp (Acusp m h k / z))⁻¹ ^ lam := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  rw [fModT_eq_Gm, norm_pow, norm_inv, norm_mul, norm_exp_ratio, hexp, ← mul_pow, ← mul_inv]
  apply pow_le_pow_left₀ (by positivity)
  apply inv_anti₀ (by positivity)
  have h1 : 1 ≤ Real.exp (3 * π * z / (k * m)) := Real.one_le_exp (by positivity)
  nlinarith [hz.1, norm_nonneg (Gm m ((h + I * z) / k))]

end ThetaSignPatterns
