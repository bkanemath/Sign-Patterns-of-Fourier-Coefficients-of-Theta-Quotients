import ThetaSignPatterns.External
import ThetaSignPatterns.Expansion

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Theta quotients as products (uses the triple product E2.3)
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-! ## Products `∏ (1 - x^{e n})` -/

/-- `HasProd` of a termwise quotient. -/
theorem hasProd_div₀ {f g : ℕ → ℂ} {a b : ℂ} (hf : HasProd f a) (hg : HasProd g b)
    (hb : b ≠ 0) : HasProd (fun n => f n / g n) (a / b) := by
  unfold HasProd at *
  simp_rw [Finset.prod_div_distrib]
  exact hf.div hg hb

theorem norm_cexp_two_pi_I_lt_one {w : ℂ} (hw : 0 < w.im) : ‖cexp (2 * π * I * w)‖ < 1 := by
  have h : (2 * π * I * w).re < 0 := by
    have : (2 * π * I * w).re = -(2 * π * w.im) := by simp [Complex.mul_re]
    rw [this, neg_lt_zero]; positivity
  simpa [Complex.norm_exp] using Real.exp_lt_exp.2 h

theorem summable_norm_pow_of_le {x : ℂ} (hx : ‖x‖ < 1) {e : ℕ → ℕ} (he : ∀ n, n ≤ e n) :
    Summable (fun n => ‖-x ^ e n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg x) hx)
  rw [norm_neg, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hx.le (he n)

/-- `∏ (1 - x^{e n})` converges for `|x| < 1` and `e n ≥ n`. -/
theorem multipliable_one_sub_pow {x : ℂ} (hx : ‖x‖ < 1) {e : ℕ → ℕ} (he : ∀ n, n ≤ e n) :
    Multipliable (fun n => 1 - x ^ e n) := by
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable (summable_norm_pow_of_le hx he)

theorem one_sub_pow_ne_zero_of_ne {x : ℂ} (hx : ‖x‖ < 1) {k : ℕ} (hk : k ≠ 0) : 1 - x ^ k ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := congrArg norm h
  rw [norm_one, norm_pow] at this
  exact (pow_lt_one₀ (norm_nonneg x) hx hk).ne' this

/-- `∏ (1 - x^{e n}) ≠ 0` for `|x| < 1` and `e n ≥ n + 1`. -/
theorem tprod_one_sub_pow_ne_zero {x : ℂ} (hx : ‖x‖ < 1) {e : ℕ → ℕ} (he : ∀ n, n + 1 ≤ e n) :
    ∏' n, (1 - x ^ e n) ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun n => -x ^ e n)
    (fun n => by simpa [← sub_eq_add_neg] using one_sub_pow_ne_zero_of_ne hx (k := e n) (by
      have := he n; omega))
    (summable_norm_pow_of_le hx (fun n => by have := he n; omega))
  simpa [sub_eq_add_neg] using this

theorem hasProd_one_sub_pow {x : ℂ} (hx : ‖x‖ < 1) {e : ℕ → ℕ} (he : ∀ n, n ≤ e n) :
    HasProd (fun n => 1 - x ^ e n) (∏' n, (1 - x ^ e n)) :=
  (multipliable_one_sub_pow hx he).hasProd

/-! ## The triple product with `Q = x^m` -/

theorem cexp_eq_pow_of_int {m : ℕ} {w T : ℂ} (hT : ∃ n : ℤ, (m : ℂ) * w - T = n) :
    cexp (2 * π * I * T) = cexp (2 * π * I * w) ^ m := by
  obtain ⟨k, hk⟩ := hT
  have hT' : T = m * w - k := by linear_combination -hk
  have h1 : 2 * π * I * ((m : ℂ) * w - k) = (m : ℂ) * (2 * π * I * w) + ((-k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [hT', h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_nat_mul]

theorem im_pos_of_int {m : ℕ} (hm : 1 ≤ m) {w T : ℂ} (hw : 0 < w.im)
    (hT : ∃ n : ℤ, (m : ℂ) * w - T = n) : 0 < T.im := by
  obtain ⟨k, hk⟩ := hT
  have hT' : T = m * w - k := by linear_combination -hk
  rw [hT']
  simp
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

/-- The triple product for `ϑ(jw;T)`, `x = e^{2πiw}`, `e^{2πiT} = x^m`. -/
theorem theta_mul_eq (H : ExternalResults) (m j : ℕ) (hj : 1 ≤ j) (hjm : j < m) (w T : ℂ)
    (hw : 0 < w.im) (hT : ∃ n : ℤ, (m : ℂ) * w - T = n) :
    theta (j * w) T = -I * cexp (π * I * T / 4) * cexp (-(π * I * (j * w))) *
      ((∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (m * n + m))) *
       (∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (m * n + j))) *
       (∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (m * n + m - j)))) := by
  have hQ := cexp_eq_pow_of_int hT
  have hζ : cexp (2 * π * I * (j * w)) = cexp (2 * π * I * w) ^ j := by
    rw [← Complex.exp_nat_mul]; ring_nf
  rw [H.thetaTripleProduct _ _ (im_pos_of_int (by omega) hw hT), hζ, hQ]
  set x := cexp (2 * π * I * w) with hx
  have hx0 : x ≠ 0 := Complex.exp_ne_zero _
  have hxl : ‖x‖ < 1 := norm_cexp_two_pi_I_lt_one hw
  congr 1
  have h1 : ∀ n : ℕ, (x ^ m) ^ (n + 1) = x ^ (m * n + m) := fun n => by ring
  have h2 : ∀ n : ℕ, x ^ j * (x ^ m) ^ n = x ^ (m * n + j) := fun n => by ring
  have h3 : ∀ n : ℕ, (x ^ j)⁻¹ * (x ^ m) ^ (n + 1) = x ^ (m * n + m - j) := fun n => by
    rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hx0), ← pow_add, ← pow_mul]
    congr 1
    have : j ≤ m * n + m := by have := Nat.le_mul_of_pos_left n (show 0 < m by omega); omega
    rw [Nat.add_sub_of_le this]; ring
  simp_rw [h3, h2, h1]
  have hle : ∀ n, n ≤ m * n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have mA := multipliable_one_sub_pow hxl (e := fun n => m * n + m) (fun n => by have := hle n; omega)
  have mB := multipliable_one_sub_pow hxl (e := fun n => m * n + j) (fun n => by have := hle n; omega)
  have mC := multipliable_one_sub_pow hxl (e := fun n => m * n + m - j)
    (fun n => by have := hle n; omega)
  rw [(mA.mul mB).tprod_mul mC, mA.tprod_mul mB]


theorem qPochInf_pow_eq (q : ℂ) (k : ℕ) :
    qPochInf (q ^ k) (q ^ k) = ∏' n : ℕ, (1 - q ^ (k * n + k)) := by
  unfold qPochInf
  congr 1
  funext n
  ring

/-- Nonvanishing of `ϑ(w;T)` and `ϑ(2w;T)` when `mw - T ∈ ℤ`, `Im w > 0`. -/
theorem theta_ne_zero_of (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) (w T : ℂ) (hw : 0 < w.im)
    (hT : ∃ n : ℤ, (m : ℂ) * w - T = n) : theta w T ≠ 0 ∧ theta (2 * w) T ≠ 0 := by
  have hxl := norm_cexp_two_pi_I_lt_one hw
  have hle : ∀ n, n ≤ m * n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have hne : ∀ j : ℕ, 1 ≤ j → j < m → theta (j * w) T ≠ 0 := by
    intro j hj hjm
    rw [theta_mul_eq H m j hj hjm w T hw hT]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 I_ne_zero)
      (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
    all_goals exact tprod_one_sub_pow_ne_zero hxl (fun n => by have := hle n; omega)
  exact ⟨by simpa using hne 1 le_rfl (by omega), by simpa using hne 2 (by norm_num) (by omega)⟩

/-- `F_m(e^{2πiw}) = e^{-πiw} ϑ(w;T)/ϑ(2w;T)` when `mw - T ∈ ℤ`, `Im w > 0`. -/
theorem Fan_eq_theta (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) (w T : ℂ) (hw : 0 < w.im)
    (hT : ∃ n : ℤ, (m : ℂ) * w - T = n) :
    Fan m (cexp (2 * π * I * w)) = cexp (-(π * I * w)) * theta w T / theta (2 * w) T := by
  have hxl := norm_cexp_two_pi_I_lt_one hw
  have hle : ∀ n, n ≤ m * n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have h1 := theta_mul_eq H m 1 le_rfl (by omega) w T hw hT
  have h2 := theta_mul_eq H m 2 (by norm_num) (by omega) w T hw hT
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2
  set x := cexp (2 * π * I * w)
  have hA : ∏' n : ℕ, (1 - x ^ (m * n + m)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero hxl (fun n => by have := hle n; omega)
  have hB2 : ∏' n : ℕ, (1 - x ^ (m * n + 2)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero hxl (fun n => by have := hle n; omega)
  have hC2 : ∏' n : ℕ, (1 - x ^ (m * n + m - 2)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero hxl (fun n => by have := hle n; omega)
  have hF : Fan m x = (∏' n : ℕ, (1 - x ^ (m * n + 1))) * (∏' n : ℕ, (1 - x ^ (m * n + m - 1))) /
      ((∏' n : ℕ, (1 - x ^ (m * n + 2))) * (∏' n : ℕ, (1 - x ^ (m * n + m - 2)))) := by
    have := hasProd_div₀
      ((hasProd_one_sub_pow hxl (e := fun n => m * n + 1) (fun n => by have := hle n; omega)).mul
        (hasProd_one_sub_pow hxl (e := fun n => m * n + m - 1) (fun n => by have := hle n; omega)))
      ((hasProd_one_sub_pow hxl (e := fun n => m * n + 2) (fun n => by have := hle n; omega)).mul
        (hasProd_one_sub_pow hxl (e := fun n => m * n + m - 2) (fun n => by have := hle n; omega)))
      (mul_ne_zero hB2 hC2)
    unfold Fan factorFan
    exact this.tprod_eq
  have he : cexp (-(π * I * (2 * w))) = cexp (-(π * I * w)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; ring_nf
  rw [hF, h1, h2, he]
  have hE := Complex.exp_ne_zero (-(π * I * w))
  have hE' := Complex.exp_ne_zero (π * I * T / 4)
  field_simp

/-- `ϑ(τ;mτ) e^{πiτ/m} / (ϑ(2τ;mτ) e^{4πiτ/m}) = e^{πiτ(m-3)/m} F_m(q)`. -/
theorem fMod_base_eq (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    (cexp (π * I * τ / m) * theta τ (m * τ)) / (cexp (4 * π * I * τ / m) * theta (2 * τ) (m * τ)) =
      cexp (π * I * τ * ((m : ℂ) - 3) / m) * Fan m (cexp (2 * π * I * τ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hT : ∃ n : ℤ, (m : ℂ) * τ - m * τ = n := ⟨0, by simp⟩
  have hF := Fan_eq_theta H m hm τ (m * τ) hτ hT
  have h2 := (theta_ne_zero_of H m hm τ (m * τ) hτ hT).2
  set F := Fan m (cexp (2 * π * I * τ))
  have hθ : theta τ (m * τ) = cexp (π * I * τ) * F * theta (2 * τ) (m * τ) := by
    rw [hF, mul_assoc, div_mul_cancel₀ _ h2, ← mul_assoc, ← Complex.exp_add]
    simp
  have key : cexp (π * I * τ * ((m : ℂ) - 3) / m) * cexp (4 * π * I * τ / m) =
      cexp (π * I * τ / m) * cexp (π * I * τ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    ring
  rw [hθ, div_eq_iff (mul_ne_zero (Complex.exp_ne_zero _) h2)]
  linear_combination (-(F * theta (2 * τ) (m * τ))) * key

theorem deltaMod_exponent (m ℓ : ℕ) (hm : 3 ≤ m) (τ : ℂ) :
    (ℓ : ℂ) * (π * I * τ * ((m : ℂ) - 3) / m) = 2 * π * I * deltaMod m ℓ * τ := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold deltaMod
  push_cast
  field_simp

/-- `f_{m,𝓁}(τ) = e^{2πiδτ} F_m(q)^𝓁`. -/
theorem fMod_eq (H : ExternalResults) (m ℓ : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    fMod m ℓ τ = cexp (2 * π * I * deltaMod m ℓ * τ) * Fan m (cexp (2 * π * I * τ)) ^ ℓ := by
  rw [fMod, fMod_base_eq H m hm τ hτ, mul_pow, ← Complex.exp_nat_mul,
    deltaMod_exponent m ℓ hm τ]

/-- `f̃_{m,λ}(τ) = e^{-2πiδτ} F̃_m(q)^λ`. -/
theorem fModT_eq (H : ExternalResults) (m lam : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    fModT m lam τ =
      cexp (-(2 * π * I * deltaMod m lam * τ)) * Ftan m (cexp (2 * π * I * τ)) ^ lam := by
  rw [fModT, ← inv_div, fMod_base_eq H m hm τ hτ, mul_inv, ← Complex.exp_neg,
    ← Ftan_eq_inv m hm _ (norm_cexp_two_pi_I_lt_one hτ), mul_pow, ← Complex.exp_nat_mul,
    mul_neg, deltaMod_exponent m lam hm τ]

theorem hasSum_fMod (H : ExternalResults) (m ℓ : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (coeffC m ℓ n : ℂ) * cexp (2 * π * I * ((n : ℂ) + deltaMod m ℓ) * τ))
      (fMod m ℓ τ) := by
  rw [fMod_eq H m ℓ hm τ hτ]
  have h := (hasSum_coeffC m ℓ hm _ (norm_cexp_two_pi_I_lt_one hτ)).mul_left
    (cexp (2 * π * I * deltaMod m ℓ * τ))
  refine (funext fun n => ?_ : (fun n : ℕ => (coeffC m ℓ n : ℂ) *
    cexp (2 * π * I * ((n : ℂ) + deltaMod m ℓ) * τ)) = _) ▸ h
  rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem hasSum_fModT (H : ExternalResults) (m lam : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
        (coeffGamma m lam n : ℂ) * cexp (2 * π * I * ((n : ℂ) + ((-deltaMod m lam : ℝ) : ℂ)) * τ))
      (fModT m lam τ) := by
  rw [fModT_eq H m lam hm τ hτ]
  have h := (hasSum_coeffGamma m lam hm _ (norm_cexp_two_pi_I_lt_one hτ)).mul_left
    (cexp (-(2 * π * I * deltaMod m lam * τ)))
  refine (funext fun n => ?_ : (fun n : ℕ => (coeffGamma m lam n : ℂ) *
    cexp (2 * π * I * ((n : ℂ) + ((-deltaMod m lam : ℝ) : ℂ)) * τ)) = _) ▸ h
  rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Nonvanishing needed in Lemma 4.2. -/
theorem Fan_neg_ne_zero (H : ExternalResults) (m : ℕ) (hm : 4 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    theta τ (m * τ) ≠ 0 ∧ theta (2 * τ) (m * τ) ≠ 0 ∧
      qPochInf (cexp (2 * π * I * τ) ^ (2 * m)) (cexp (2 * π * I * τ) ^ (2 * m)) ≠ 0 := by
  have hT : ∃ n : ℤ, (m : ℂ) * τ - m * τ = n := ⟨0, by simp⟩
  obtain ⟨h1, h2⟩ := theta_ne_zero_of H m (by omega) τ (m * τ) hτ hT
  refine ⟨h1, h2, ?_⟩
  rw [qPochInf_pow_eq]
  exact tprod_one_sub_pow_ne_zero (norm_cexp_two_pi_I_lt_one hτ) (fun n => by
    have := Nat.le_mul_of_pos_left n (show 0 < 2 * m by omega); omega)

/-- For even `m`, `u_{m,n}(-q) = (1-q^{2mn+2})(1-q^{2mn+2m-2})` divided by
`(1-q^{mn+1})(1-q^{mn+m-1})(1-q^{mn+2})(1-q^{mn+m-2})`. -/
theorem factorFan_neg (m n : ℕ) (hm : 4 ≤ m) (hev : Even m) (q : ℂ) (hq : ‖q‖ < 1) :
    factorFan m n (-q) = (1 - q ^ (2 * m * n + 2)) * (1 - q ^ (2 * m * n + 2 * m - 2)) /
      (((1 - q ^ (m * n + 1)) * (1 - q ^ (m * n + m - 1))) *
        ((1 - q ^ (m * n + 2)) * (1 - q ^ (m * n + m - 2)))) := by
  obtain ⟨k, hk⟩ := hev
  have hmn : m * n = 2 * (k * n) := by rw [hk]; ring
  have h2mn : 2 * m * n = 2 * (m * n) := by ring
  have ho1 : Odd (m * n + 1) := ⟨k * n, by omega⟩
  have ho2 : Odd (m * n + m - 1) := ⟨k * n + k - 1, by omega⟩
  have he1 : Even (m * n + 2) := ⟨k * n + 1, by omega⟩
  have he2 : Even (m * n + m - 2) := ⟨k * n + k - 1, by omega⟩
  have hp1 : q ^ (2 * m * n + 2) = (q ^ (m * n + 1)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  have hp2 : q ^ (2 * m * n + 2 * m - 2) = (q ^ (m * n + m - 1)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  have n1 := one_sub_pow_ne_zero_of_ne hq (k := m * n + 1) (by omega)
  have n2 := one_sub_pow_ne_zero_of_ne hq (k := m * n + m - 1) (by omega)
  have n3 := one_sub_pow_ne_zero_of_ne hq (k := m * n + 2) (by omega)
  have n4 := one_sub_pow_ne_zero_of_ne hq (k := m * n + m - 2) (by omega)
  unfold factorFan
  rw [Odd.neg_pow ho1, Odd.neg_pow ho2, Even.neg_pow he1, Even.neg_pow he2, hp1, hp2]
  field_simp
  ring

/-- The identity behind Lemma 4.2: for even `m`,
`F_m(-q) = -i e^{-πiτ} (q^m;q^m)²_∞ ϑ(2τ;2mτ) / ((q^{2m};q^{2m})_∞ ϑ(τ;mτ) ϑ(2τ;mτ))`. -/
theorem Fan_neg_eq (H : ExternalResults) (m : ℕ) (hm : 4 ≤ m) (hev : Even m) (τ : ℂ)
    (hτ : 0 < τ.im) :
    Fan m (-cexp (2 * π * I * τ)) =
      -I * cexp (-(π * I * τ)) *
        qPochInf (cexp (2 * π * I * τ) ^ m) (cexp (2 * π * I * τ) ^ m) ^ 2 *
        theta (2 * τ) (2 * m * τ) /
      (qPochInf (cexp (2 * π * I * τ) ^ (2 * m)) (cexp (2 * π * I * τ) ^ (2 * m)) *
        theta τ (m * τ) * theta (2 * τ) (m * τ)) := by
  have hq := norm_cexp_two_pi_I_lt_one hτ
  have hle : ∀ n, n ≤ m * n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have hle2 : ∀ n, n ≤ 2 * m * n := fun n => Nat.le_mul_of_pos_left n (by omega)
  have hT : ∃ n : ℤ, (m : ℂ) * τ - m * τ = n := ⟨0, by simp⟩
  have hT2 : ∃ n : ℤ, ((2 * m : ℕ) : ℂ) * τ - 2 * m * τ = n := ⟨0, by push_cast; ring⟩
  have h1 := theta_mul_eq H m 1 le_rfl (by omega) τ (m * τ) hτ hT
  have h2 := theta_mul_eq H m 2 (by norm_num) (by omega) τ (m * τ) hτ hT
  have h3 := theta_mul_eq H (2 * m) 2 (by norm_num) (by omega) τ (2 * m * τ) hτ hT2
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2 h3
  set q := cexp (2 * π * I * τ)
  have hF : Fan m (-q) = (∏' n : ℕ, (1 - q ^ (2 * m * n + 2))) *
      (∏' n : ℕ, (1 - q ^ (2 * m * n + 2 * m - 2))) /
      (((∏' n : ℕ, (1 - q ^ (m * n + 1))) * (∏' n : ℕ, (1 - q ^ (m * n + m - 1)))) *
        ((∏' n : ℕ, (1 - q ^ (m * n + 2))) * (∏' n : ℕ, (1 - q ^ (m * n + m - 2))))) := by
    have := hasProd_div₀
      ((hasProd_one_sub_pow hq (e := fun n => 2 * m * n + 2) (fun n => by have := hle2 n; omega)).mul
        (hasProd_one_sub_pow hq (e := fun n => 2 * m * n + 2 * m - 2)
          (fun n => by have := hle2 n; omega)))
      (((hasProd_one_sub_pow hq (e := fun n => m * n + 1) (fun n => by have := hle n; omega)).mul
        (hasProd_one_sub_pow hq (e := fun n => m * n + m - 1)
          (fun n => by have := hle n; omega))).mul
        ((hasProd_one_sub_pow hq (e := fun n => m * n + 2) (fun n => by have := hle n; omega)).mul
        (hasProd_one_sub_pow hq (e := fun n => m * n + m - 2)
          (fun n => by have := hle n; omega))))
      (mul_ne_zero
        (mul_ne_zero (tprod_one_sub_pow_ne_zero hq (fun n => by have := hle n; omega))
          (tprod_one_sub_pow_ne_zero hq (fun n => by have := hle n; omega)))
        (mul_ne_zero (tprod_one_sub_pow_ne_zero hq (fun n => by have := hle n; omega))
          (tprod_one_sub_pow_ne_zero hq (fun n => by have := hle n; omega))))
    unfold Fan
    simp_rw [factorFan_neg m _ hm hev q hq]
    exact this.tprod_eq
  have he1 : cexp (π * I * (2 * m * τ) / 4) = cexp (π * I * (m * τ) / 4) ^ 2 := by
    rw [← Complex.exp_nat_mul]; ring_nf
  have he2 : cexp (-(π * I * (2 * τ))) = cexp (-(π * I * τ)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; ring_nf
  rw [hF, qPochInf_pow_eq, qPochInf_pow_eq, h1, h2, h3, he1, he2]
  have nA := tprod_one_sub_pow_ne_zero hq (e := fun n => m * n + m) (fun n => by have := hle n; omega)
  have nA' := tprod_one_sub_pow_ne_zero hq (e := fun n => 2 * m * n + 2 * m)
    (fun n => by have := hle2 n; omega)
  have nB1 := tprod_one_sub_pow_ne_zero hq (e := fun n => m * n + 1) (fun n => by have := hle n; omega)
  have nC1 := tprod_one_sub_pow_ne_zero hq (e := fun n => m * n + m - 1)
    (fun n => by have := hle n; omega)
  have nB2 := tprod_one_sub_pow_ne_zero hq (e := fun n => m * n + 2) (fun n => by have := hle n; omega)
  have nC2 := tprod_one_sub_pow_ne_zero hq (e := fun n => m * n + m - 2)
    (fun n => by have := hle n; omega)
  have hE := Complex.exp_ne_zero (-(π * I * τ))
  have hE' := Complex.exp_ne_zero (π * I * (m * τ) / 4)
  field_simp

end ThetaSignPatterns
