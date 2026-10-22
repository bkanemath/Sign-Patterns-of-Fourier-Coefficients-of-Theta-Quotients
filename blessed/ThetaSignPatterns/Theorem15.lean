import ThetaSignPatterns.Modularity
import ThetaSignPatterns.CuspGrowth
import ThetaSignPatterns.LocalConstants
import ThetaSignPatterns.MainTerm

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Theorem 1.5 and Corollary 1.6
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- `m ≡ ±1 (mod 6)` with the corresponding signs. -/
private lemma m_cases (m : ℕ) (hcop : Nat.Coprime m 6) :
    (∃ q : ℕ, m = 6 * q + 1 ∧ epsZ m = 1 ∧ epsM m = 1) ∨
      (∃ q : ℕ, m = 6 * q + 5 ∧ epsZ m = -1 ∧ epsM m = -1) := by
  have h6 : m % 6 = 1 ∨ m % 6 = 5 := by
    have hg : Nat.gcd (m % 6) 6 = 1 := by
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcop
    have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases h : m % 6 <;> simp_all
  rcases h6 with h | h
  · left; exact ⟨m / 6, by omega, by simp [epsZ, h], by simp [epsM, h]⟩
  · right; exact ⟨m / 6, by omega, by simp [epsZ, h], by simp [epsM, h]⟩

private lemma epsZ_cast (m : ℕ) : ((epsZ m : ℤ) : ℝ) = epsM m := by
  unfold epsZ epsM; split_ifs <;> simp

/-- The phase at the dominant cusp `(m∓1)/(6m)`: `Re(C̃_m^λ e^{-2πinh₁/m}) = T^{[λ]}_m(n)`. -/
theorem phase_15 (m lam n : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) :
    (CT m ^ lam * cexp (-(2 * π * I * n * ((((m : ℤ) - epsZ m) / 6 : ℤ) : ℂ) / m))).re =
      Tfun m lam n := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hh : (((((m : ℤ) - epsZ m) / 6 : ℤ) : ℝ)) = ((m : ℝ) - epsM m) / 6 := by
    rcases m_cases m hcop with ⟨q, rfl, hz, hr⟩ | ⟨q, rfl, hz, hr⟩
    · rw [hz, hr]; push_cast
      rw [show (6 * (q : ℤ) + 1 - 1) = q * 6 by ring, Int.mul_ediv_cancel _ (by norm_num)]
      push_cast; ring
    · rw [hz, hr]; push_cast
      rw [show (6 * (q : ℤ) + 5 - -1) = (q + 1) * 6 by ring, Int.mul_ediv_cancel _ (by norm_num)]
      push_cast; ring
  have hh' : (((((m : ℤ) - epsZ m) / 6 : ℤ) : ℂ)) = (((m : ℝ) - epsM m) / 6 : ℝ) := by
    rw [← hh]; push_cast; rfl
  rw [CT, ← Complex.exp_nat_mul, ← Complex.exp_add, hh']
  have : (lam : ℂ) * (π * I * (1 / 6 - (epsM m : ℂ) / (6 * m) + (epsM m : ℂ) / (m : ℂ) ^ 2)) +
      -(2 * π * I * n * ((((m : ℝ) - epsM m) / 6 : ℝ) : ℂ) / m) =
      ((π * ((lam : ℝ) / 6 - (n : ℝ) / 3 +
        epsM m * ((2 * (n : ℝ) - lam) / (6 * m) + (lam : ℝ) / (m : ℝ) ^ 2)) : ℝ) : ℂ) * I := by
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
    push_cast
    field_simp
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]
  rfl

theorem Tfun_ne_zero (m lam n : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) : Tfun m lam n ≠ 0 := by
  intro h
  unfold Tfun at h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hX : (lam : ℝ) / 6 - (n : ℝ) / 3 +
      epsM m * ((2 * (n : ℝ) - lam) / (6 * m) + (lam : ℝ) / (m : ℝ) ^ 2) = (2 * k + 1) / 2 := by
    have h' : π * ((lam : ℝ) / 6 - (n : ℝ) / 3 +
        epsM m * ((2 * (n : ℝ) - lam) / (6 * m) + (lam : ℝ) / (m : ℝ) ^ 2) - (2 * k + 1) / 2)
        = 0 := by rw [mul_sub]; linarith
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 pi_ne_zero
    · linarith
  rcases m_cases m hcop with ⟨q, rfl, -, hr⟩ | ⟨q, rfl, -, hr⟩
  · rw [hr] at hX
    have hR : (lam : ℝ) * (6 * q + 1) ^ 2 - 2 * n * (6 * q + 1) ^ 2 +
        ((2 * n - lam) * (6 * q + 1) + 6 * lam) = 3 * (6 * q + 1) ^ 2 * (2 * k + 1) := by
      push_cast at hX
      field_simp at hX
      linarith
    have hZ : (lam : ℤ) * (6 * q + 1) ^ 2 - 2 * n * (6 * q + 1) ^ 2 +
        ((2 * n - lam) * (6 * q + 1) + 6 * lam) = 3 * (6 * q + 1) ^ 2 * (2 * k + 1) := by
      exact_mod_cast hR
    have : (2 : ℤ) * (3 * lam * q * (6 * q + 1) - 6 * n * q * (6 * q + 1) + 3 * lam) =
        2 * (3 * (6 * q + 1) ^ 2 * k + 54 * q ^ 2 + 18 * q + 1) + 1 := by
      linear_combination hZ
    omega
  · rw [hr] at hX
    have hR : (lam : ℝ) * (6 * q + 5) ^ 2 - 2 * n * (6 * q + 5) ^ 2 -
        ((2 * n - lam) * (6 * q + 5) + 6 * lam) = 3 * (6 * q + 5) ^ 2 * (2 * k + 1) := by
      push_cast at hX
      field_simp at hX
      linarith
    have hZ : (lam : ℤ) * (6 * q + 5) ^ 2 - 2 * n * (6 * q + 5) ^ 2 -
        ((2 * n - lam) * (6 * q + 5) + 6 * lam) = 3 * (6 * q + 5) ^ 2 * (2 * k + 1) := by
      exact_mod_cast hR
    have : (2 : ℤ) * (lam * (6 * q + 5) * (3 * q + 3) - 2 * n * (6 * q + 5) * (3 * q + 3)
        - 3 * lam) = 2 * (3 * (6 * q + 5) ^ 2 * k + 54 * q ^ 2 + 90 * q + 37) + 1 := by
      linear_combination hZ
    omega

private lemma Tfun_add_period (m lam n : ℕ) (hm : 5 ≤ m) :
    Tfun m lam (n + 6 * m) = Tfun m lam n := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold Tfun
  rw [← Real.cos_add_int_mul_two_pi _ (m - epsZ m)]
  congr 1
  rw [← epsZ_cast]
  push_cast
  field_simp
  ring

private lemma Tfun_mod (m lam n : ℕ) (hm : 5 ≤ m) : Tfun m lam n = Tfun m lam (n % (6 * m)) := by
  have key : ∀ k r : ℕ, Tfun m lam (r + 6 * m * k) = Tfun m lam r := by
    intro k r
    induction k with
    | zero => simp
    | succ k ih => rw [show r + 6 * m * (k + 1) = (r + 6 * m * k) + 6 * m by ring,
        Tfun_add_period m lam _ hm, ih]
  conv_lhs => rw [← Nat.mod_add_div n (6 * m)]
  exact key _ _

theorem Tfun_bound (m lam : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, κ ≤ |Tfun m lam n| := by
  have hne : (Finset.range (6 * m)).Nonempty := ⟨0, by simp; omega⟩
  refine ⟨(Finset.range (6 * m)).inf' hne (fun n => |Tfun m lam n|), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro b _
    exact abs_pos.2 (Tfun_ne_zero m lam b hm hcop)
  · intro n
    rw [Tfun_mod m lam n hm]
    exact Finset.inf'_le _ (Finset.mem_range.2 (Nat.mod_lt _ (by omega)))

private lemma im_cusp_pos (h : ℤ) (k : ℕ) (hk : 0 < k) (z : ℝ) (hz : 0 < z) :
    0 < (((h : ℂ) + I * z) / k).im := by
  have : (((h : ℂ) + I * z) / k).im = z / k := by
    simp [Complex.div_im, Complex.normSq]
    field_simp
  rw [this]; positivity

/-- The limit at a dominant cusp. -/
private lemma tendsto_dom (H : ExternalResults) (m lam : ℕ) (hm : 5 ≤ m) (h : ℤ) (L : ℂ)
    (hF : Tendsto (fun z : ℝ => Ftan m (cexp (2 * π * I * ((h : ℂ) + I * z) / m)) *
        cexp (-((m * LamT m / z : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun z : ℝ => fModT m lam ((h + I * z) / m) *
        cexp (-(((lam * LamT m) * m / z : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (cexp (2 * π * I * ((-deltaMod m lam : ℝ) : ℂ) * h / m) * L ^ lam)) := by
  have hP : Tendsto (fun z : ℝ => cexp (-(2 * π * I * (deltaMod m lam : ℂ) * ((h + I * z) / m))))
      (𝓝[>] 0) (𝓝 (cexp (2 * π * I * ((-deltaMod m lam : ℝ) : ℂ) * h / m))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun z : ℝ =>
        cexp (-(2 * π * I * (deltaMod m lam : ℂ) * ((h + I * z) / m)))) := by fun_prop
    convert hc.tendsto 0 using 2
    push_cast
    ring_nf
  refine (hP.mul (hF.pow lam)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [fModT_eq H m lam (by omega) _ (im_cusp_pos h m (by omega) z hz), mul_pow,
    ← Complex.exp_nat_mul (-((m * LamT m / z : ℝ) : ℂ))]
  have e1 : cexp (2 * π * I * ((h : ℂ) + I * z) / m) = cexp (2 * π * I * ((h + I * z) / m)) := by
    ring_nf
  have e2 : (lam : ℂ) * (-((m * LamT m / z : ℝ) : ℂ)) = -(((lam * LamT m) * m / z : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2]
  ring

/-- **Theorem 1.5** (asymptotics). -/
theorem theorem_1_5 (H : ExternalResults) (m lam : ℕ) (hm : 3 < m) (hcop : Nat.Coprime m 6)
    (hlam : 0 < lam) :
    (fun n : ℕ => (coeffGamma m lam n : ℝ)) ~[atTop] (fun n : ℕ =>
      ((1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m)) ^ (1 / 4 : ℝ) * Tfun m lam n *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m))) /
        (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hm5 : 5 ≤ m := by
    rcases m_cases m hcop with ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩ <;> omega
  have hodd : Odd m := by
    rcases m_cases m hcop with ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩
    · exact ⟨3 * q, by ring⟩
    · exact ⟨3 * q + 2, by ring⟩
  have hsum : ((m : ℤ) - epsZ m) / 6 + (5 * (m : ℤ) + epsZ m) / 6 = m := by
    rcases m_cases m hcop with ⟨q, rfl, hz, -⟩ | ⟨q, rfl, hz, -⟩ <;> rw [hz] <;> push_cast <;> omega
  have hne : ((m : ℤ) - epsZ m) / 6 ≠ (5 * (m : ℤ) + epsZ m) / 6 := by
    rcases m_cases m hcop with ⟨q, rfl, hz, -⟩ | ⟨q, rfl, hz, -⟩ <;> rw [hz] <;> push_cast <;> omega
  have hm0 : (0 : ℝ) < m := by positivity
  have hLamT : 0 < LamT m := by
    unfold LamT
    have : (1 : ℝ) < (m : ℝ) ^ 2 := by
      have : (5 : ℝ) ≤ m := by exact_mod_cast hm5
      nlinarith
    have : 0 < (m : ℝ) ^ 2 - 1 := by linarith
    positivity
  have hlamR : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hΛ : 0 < (lam : ℝ) * LamT m := mul_pos hlamR hLamT
  obtain ⟨κ, hκ, hκb⟩ := Tfun_bound m lam hm5 hcop
  let C : ℤ × ℕ → ℂ := fun p =>
    if p.1 = ((m : ℤ) - epsZ m) / 6 then
      cexp (2 * π * I * ((-deltaMod m lam : ℝ) : ℂ) * ((((m : ℤ) - epsZ m) / 6 : ℤ) : ℂ) / m) *
        CT m ^ lam
    else
      cexp (2 * π * I * ((-deltaMod m lam : ℝ) : ℂ) * ((((5 * (m : ℤ) + epsZ m) / 6 : ℤ) : ℂ)) / m)
        * starRingEnd ℂ (CT m ^ lam)
  have E := H.rademacherZuckerman (fModT m lam) (fun n => ((coeffGamma m lam n : ℝ) : ℂ))
    (-deltaMod m lam) ((lam : ℝ) * LamT m) (lam * LamT' m) (domT m) C
    (fModT_isWHModular H m lam (by omega))
    (fun τ hτ => by simpa using hasSum_fModT H m lam (by omega) τ hτ)
    hΛ (mul_lt_mul_of_pos_left (LamT'_lt m hm5) hlamR)
    (domT_reduced m hm5 hcop) ?_ ?_
  rotate_left
  · intro p hp
    simp only [domT, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · have := tendsto_dom H m lam hm5 _ _ (Ftan_dom₁ H m hm5 hcop)
      simpa [C] using this
    · have := tendsto_dom H m lam hm5 _ _ (Ftan_dom₂ H m hm5 hcop)
      simpa [C, hne.symm, map_pow] using this
  · intro p hp hpD
    obtain ⟨K, hK⟩ := fModT_cusp_bound H m lam (by omega) hodd p.1 p.2
      (by have := hp.1; have := hp.2.1; omega) hp.2.2
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK, self_mem_nhdsWithin] with z hz hz0
    have hA := neg_Acusp_le_LamT' m hm5 hcop p hp hpD
    have hz0' : (0 : ℝ) < z := hz0
    calc ‖fModT m lam ((p.1 + I * (z : ℂ)) / p.2)‖
        ≤ K * Real.exp (-(lam * Acusp m p.1 p.2) / z) := hz
      _ ≤ max K 0 * Real.exp (-(lam * Acusp m p.1 p.2) / z) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max K 0 * Real.exp (lam * LamT' m * p.2 / z) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          apply Real.exp_le_exp.2
          apply div_le_div_of_nonneg_right _ hz0'.le
          nlinarith
  have ho := E.congr_left (fun n => by
    rw [show domT m = {((((m : ℤ) - epsZ m) / 6), m), ((5 * (m : ℤ) + epsZ m) / 6, m)} from rfl,
      Finset.sum_pair (by simpa using hne)])
  simp only [C, ↓reduceIte, if_neg hne.symm] at ho
  have T := two_cusp H ((lam : ℝ) * LamT m) (-deltaMod m lam) hΛ _ _ m (by omega) hsum
    (CT m ^ lam) (fun n => (coeffGamma m lam n : ℝ)) κ hκ
    (fun n => by rw [phase_15 m lam n hm5 hcop]; exact hκb n) ho
  refine T.congr_right (Eventually.of_forall fun n => ?_)
  simp only
  rw [phase_15 m lam n hm5 hcop, Real.rpow_neg (Nat.cast_nonneg n)]
  have h1 : 2 * ((lam : ℝ) * LamT m) / π = (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m) := by
    unfold LamT
    field_simp
    ring
  have h2 : Real.sqrt (8 * π * ((lam : ℝ) * LamT m) * n) =
      π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m)) := by
    rw [show 8 * π * ((lam : ℝ) * LamT m) * n =
        π ^ 2 * (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m)) by
      unfold LamT; field_simp; ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq pi_pos.le]
  rw [h1, h2]
  ring

private lemma sign_pos_mul (c x : ℝ) (hc : 0 < c) : Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private lemma sign_neg_one_pow_mul (k : ℕ) (x : ℝ) :
    Real.sign ((-1) ^ k * x) = (-1) ^ k * Real.sign x := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h]
  · simp
  · rw [neg_one_mul, neg_one_mul, Real.sign_neg]

/-- **Theorem 1.5** (sign): `sgn γ^{[λ]}_m(n) = sgn T^{[λ]}_m(n)` for `n ≫ 1`. -/
theorem theorem_1_5_sign (H : ExternalResults) (m lam : ℕ) (hm : 3 < m)
    (hcop : Nat.Coprime m 6) (hlam : 0 < lam) :
    ∀ᶠ n : ℕ in atTop, Real.sign (coeffGamma m lam n : ℝ) = Real.sign (Tfun m lam n) := by
  have hm5 : 5 ≤ m := by
    rcases m_cases m hcop with ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩ <;> omega
  have hP : 0 < (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m) := by
    have : (5 : ℝ) ≤ m := by exact_mod_cast hm5
    have h1 : 0 < 1 - 1 / (m : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    have : (0 : ℝ) < lam := by exact_mod_cast hlam
    positivity
  have hv : ∀ᶠ n : ℕ in atTop,
      ((1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam / (6 * m)) ^ (1 / 4 : ℝ) * Tfun m lam n *
        Real.exp (π * Real.sqrt (2 * (1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ)) * lam * n / (3 * m))) /
        (n : ℝ) ^ (3 / 4 : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := Tfun_ne_zero m lam n hm5 hcop
    have := Real.rpow_pos_of_pos hP (1 / 4)
    have := Real.rpow_pos_of_pos hn' (3 / 4)
    positivity
  filter_upwards [sign_eventually_of_equiv _ _ (theorem_1_5 H m lam hm hcop hlam) hv,
    eventually_ge_atTop 1] with n hn hn1
  rw [hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [show ∀ a T b c : ℝ, a * T * b / c = (a * b / c) * T by intros; ring]
  exact sign_pos_mul _ _ (by
    have := Real.rpow_pos_of_pos hP (1 / 4)
    have := Real.rpow_pos_of_pos hn' (3 / 4)
    positivity)

/-- The integer `R = a(±m - 1)/6 + r - s` of (5.4), where `λ = 6s + a`, `0 ≤ a ≤ 5`. -/
def Rred (m lam : ℕ) (r : ℤ) : ℤ := ((lam % 6 : ℕ) : ℤ) * (epsZ m * m - 1) / 6 + r - (lam / 6 : ℕ)

private lemma Rred_eq₁ (q lam : ℕ) (r : ℤ) (h : epsZ (6 * q + 1) = 1) :
    Rred (6 * q + 1) lam r = ((lam % 6 : ℕ) : ℤ) * q + r - (lam / 6 : ℕ) := by
  unfold Rred
  rw [h, show ((lam % 6 : ℕ) : ℤ) * (1 * ((6 * q + 1 : ℕ) : ℤ) - 1) = (lam % 6 : ℕ) * q * 6 by
    push_cast; ring, Int.mul_ediv_cancel _ (by norm_num)]

private lemma Rred_eq₂ (q lam : ℕ) (r : ℤ) (h : epsZ (6 * q + 5) = -1) :
    Rred (6 * q + 5) lam r = -(((lam % 6 : ℕ) : ℤ) * (q + 1)) + r - (lam / 6 : ℕ) := by
  unfold Rred
  rw [h, show ((lam % 6 : ℕ) : ℤ) * (-1 * ((6 * q + 5 : ℕ) : ℤ) - 1) =
    -((lam % 6 : ℕ) * ((q : ℤ) + 1)) * 6 by push_cast; ring, Int.mul_ediv_cancel _ (by norm_num)]

private lemma cos_reduce (X Y : ℝ) (k K : ℤ) (h : X = Y + k * π + K * (2 * π)) :
    Real.cos X = (-1) ^ k * Real.cos Y := by
  rw [h, Real.cos_add_int_mul_two_pi, Real.cos_add_int_mul_pi]

private lemma cos_reduce' (X Y : ℝ) (k K : ℤ) (h : X = -Y + k * π + K * (2 * π)) :
    Real.cos X = (-1) ^ k * Real.cos Y := by
  rw [h, Real.cos_add_int_mul_two_pi, Real.cos_add_int_mul_pi, Real.cos_neg]

private lemma neg_one_zpow_add_eq_sub (r s : ℤ) : (-1 : ℝ) ^ (r + s) = (-1) ^ (s - r) := by
  rw [show r + s = (s - r) + 2 * r by ring, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- (5.3)–(5.4): `T^{[λ]}_m(n) = (-1)^{r+s} cos(π(R/m + λ/m²))` for `n ≡ 3r + 2mj (mod 6m)`. -/
theorem Tfun_reduce (m lam n : ℕ) (r j : ℤ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6)
    (hn : (n : ℤ) ≡ 3 * r + 2 * m * j [ZMOD 6 * m]) :
    Tfun m lam n = (-1 : ℝ) ^ (r + (lam / 6 : ℕ)) *
      Real.cos (π * ((Rred m lam r : ℝ) / m + (lam : ℝ) / (m : ℝ) ^ 2)) := by
  obtain ⟨t, ht⟩ := hn.dvd
  have hnR : (n : ℝ) = 3 * r + 2 * m * j - 6 * m * t := by
    have : (n : ℤ) = 3 * r + 2 * m * j - 6 * m * t := by linarith
    exact_mod_cast this
  have hlam : (lam : ℝ) = 6 * ((lam / 6 : ℕ) : ℝ) + ((lam % 6 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod lam 6).symm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [neg_one_zpow_add_eq_sub]
  unfold Tfun
  rcases m_cases m hcop with ⟨q, rfl, hz, hr⟩ | ⟨q, rfl, hz, hr⟩
  · rw [Rred_eq₁ q lam r hz, hr]
    apply cos_reduce _ _ _ (-2 * j * q + 6 * t * q)
    rw [hnR, hlam]
    generalize lam / 6 = s
    generalize lam % 6 = a
    push_cast
    field_simp
    ring
  · rw [Rred_eq₂ q lam r hz, hr]
    apply cos_reduce' _ _ _ (-2 * j * (q + 1) + 6 * t * (q + 1))
    rw [hnR, hlam]
    generalize lam / 6 = s
    generalize lam % 6 = a
    push_cast
    field_simp
    ring

/-- (5.5): the sign of `cos(π(R/m + ε))` for `0 < ε < 1/(2m)`. -/
theorem sign_cos_eps (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) (R : ℤ) (ε : ℝ) (hε₀ : 0 < ε)
    (hε : ε < 1 / (2 * m)) :
    Real.sign (Real.cos (π * ((R : ℝ) / m + ε))) =
      (-1) ^ chi ((m : ℤ) + 1 ≤ 2 * (R % (2 * m)) ∧ 2 * (R % (2 * m)) ≤ 3 * m - 1) := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hM : (0 : ℤ) < 2 * m := by omega
  have hρ0 : 0 ≤ R % (2 * m) := Int.emod_nonneg _ hM.ne'
  have hρ1 : R % (2 * m) < 2 * m := Int.emod_lt_of_pos _ hM
  have hRq : R = R % (2 * m) + 2 * m * (R / (2 * m)) := (Int.emod_add_mul_ediv R (2 * m)).symm
  generalize R % (2 * m) = ρ at hρ0 hρ1 hRq ⊢
  generalize R / (2 * m) = K at hRq
  subst hRq
  have hcos : Real.cos (π * (((ρ + 2 * m * K : ℤ) : ℝ) / m + ε)) =
      Real.cos (π * ((ρ : ℝ) / m + ε)) := by
    rw [← Real.cos_add_int_mul_two_pi _ (-K)]
    congr 1
    push_cast
    field_simp
    ring
  rw [hcos]
  have hεm : ε * m < 1 / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)).1 hε
    linarith
  have hεpos : 0 < ε * m := by positivity
  have hρ0' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ0
  have hρ1' : (ρ : ℝ) ≤ 2 * m - 1 := by
    have : ρ ≤ 2 * m - 1 := by omega
    exact_mod_cast this
  have hx : (ρ : ℝ) / m + ε = ((ρ : ℝ) + ε * m) / m := by field_simp
  obtain ⟨k, hk⟩ := hodd
  rcases (by omega : 2 * ρ ≤ m - 1 ∨ ((m : ℤ) + 1 ≤ 2 * ρ ∧ 2 * ρ ≤ 3 * m - 1) ∨
      3 * m + 1 ≤ 2 * ρ) with h | h | h
  · have hR : 2 * (ρ : ℝ) ≤ m - 1 := by
      have : 2 * ρ ≤ (m : ℤ) - 1 := by omega
      exact_mod_cast this
    have h1 : (ρ : ℝ) / m + ε < 1 / 2 := by
      rw [hx, div_lt_iff₀ hm0]; linarith
    have h2 : 0 < (ρ : ℝ) / m + ε := by positivity
    rw [Real.sign_of_pos, chi, if_neg (by omega)]
    · simp
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [pi_pos]
  · have hR1 : (m : ℝ) + 1 ≤ 2 * (ρ : ℝ) := by exact_mod_cast h.1
    have hR2 : 2 * (ρ : ℝ) ≤ 3 * m - 1 := by exact_mod_cast h.2
    have h1 : 1 / 2 < (ρ : ℝ) / m + ε := by
      rw [hx, lt_div_iff₀ hm0]; linarith
    have h2 : (ρ : ℝ) / m + ε < 3 / 2 := by
      rw [hx, div_lt_iff₀ hm0]; linarith
    rw [Real.sign_of_neg, chi, if_pos h]
    · simp
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> nlinarith [pi_pos]
  · have hR : 3 * (m : ℝ) + 1 ≤ 2 * (ρ : ℝ) := by exact_mod_cast h
    have h1 : 3 / 2 < (ρ : ℝ) / m + ε := by
      rw [hx, lt_div_iff₀ hm0]; linarith
    have h2 : (ρ : ℝ) / m + ε < 2 := by
      rw [hx, div_lt_iff₀ hm0]; linarith
    rw [Real.sign_of_pos, chi, if_neg (by omega)]
    · simp
    rw [← Real.cos_sub_two_pi]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [pi_pos]

private lemma emod_of_bounds (R M u : ℤ) (h0 : 0 ≤ R - M * u) (h1 : R - M * u < M) :
    R % M = R - M * u := by
  have : R = (R - M * u) + M * u := by ring
  conv_lhs => rw [this]
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

private lemma emod_cases (R M : ℤ) (h1 : -M ≤ R) (h2 : R < 3 * M) :
    ∃ u : ℤ, (u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2) ∧ R % M = R - M * u ∧ 0 ≤ R - M * u ∧
      R - M * u < M := by
  rcases (by omega : R < 0 ∨ (0 ≤ R ∧ R < M) ∨ (M ≤ R ∧ R < 2 * M) ∨ 2 * M ≤ R) with
    h | h | h | h
  · exact ⟨-1, by omega, emod_of_bounds _ _ _ (by linarith) (by linarith), by linarith,
      by linarith⟩
  · exact ⟨0, by omega, emod_of_bounds _ _ _ (by linarith) (by linarith), by linarith,
      by linarith⟩
  · exact ⟨1, by omega, emod_of_bounds _ _ _ (by linarith) (by linarith), by linarith,
      by linarith⟩
  · exact ⟨2, by omega, emod_of_bounds _ _ _ (by linarith) (by linarith), by linarith,
      by linarith⟩

private lemma jacobi_one (q : ℕ) : jacobiSym ((6 * q + 1 : ℕ) : ℤ) 3 = 1 := by
  rw [jacobiSym.mod_left, show ((6 * q + 1 : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = 1 by omega]
  exact jacobiSym.one_left 3

private lemma jacobi_five (q : ℕ) : jacobiSym ((6 * q + 5 : ℕ) : ℤ) 3 = -1 := by
  rw [jacobiSym.mod_left, show ((6 * q + 5 : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = 2 by omega]
  norm_num

private lemma c16_1_0 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 0)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 0 := by omega
  have hR : Rred m lam r = 0 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ (3 * (m : ℤ) + 3 + (lam : ℤ) ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ 9 * (m : ℤ) - 3 + (lam : ℤ)) := by
    unfold S2 S2bounds
    simp only [hmod]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (0 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_1_1 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 1)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 1 := by omega
  have hR : Rred m lam r = 1 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 - 1) * (m : ℤ) + 4 + (lam : ℤ) - 1 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 - 1) * (m : ℤ) - 2 + (lam : ℤ) - 1) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_true]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (1 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_1_2 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 2)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 2 := by omega
  have hR : Rred m lam r = 2 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 - 2 * 1) * (m : ℤ) + 5 + (lam : ℤ) - 2 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 - 2 * 1) * (m : ℤ) - 1 + (lam : ℤ) - 2) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_true]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (2 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_1_3 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 3)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 3 := by omega
  have hR : Rred m lam r = 3 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((lam : ℤ) + 3 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ 6 * (m : ℤ) + (lam : ℤ) - 3) := by
    unfold S2 S2bounds
    simp only [hmod]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    subst hq; unfold epsLam; rw [hmod, if_pos rfl, jacobi_one]
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (3 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_1_4 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 4)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 4 := by omega
  have hR : Rred m lam r = 4 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 + 2 * 1) * (m : ℤ) + 7 + (lam : ℤ) - 4 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 + 2 * 1) * (m : ℤ) + 1 + (lam : ℤ) - 4) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_true]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = -1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (4 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_1_5 (m lam q s r : ℕ) (hq : m = 6 * q + 1) (hs : lam = 6 * s + 5)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 1 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 5 := by omega
  have hR : Rred m lam r = 5 * (q : ℤ) + r - s := by
    subst hq
    rw [Rred_eq₁ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 + 1) * (m : ℤ) + 8 + (lam : ℤ) - 5 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 + 1) * (m : ℤ) + 2 + (lam : ℤ) - 5) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_true]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = -1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (5 * (q : ℤ) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_0 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 0)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 0 := by omega
  have hR : Rred m lam r = -(0 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ (3 * (m : ℤ) + 3 + (lam : ℤ) ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ 9 * (m : ℤ) - 3 + (lam : ℤ)) := by
    unfold S2 S2bounds
    simp only [hmod]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(0 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_1 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 1)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 1 := by omega
  have hR : Rred m lam r = -(1 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 - (-1)) * (m : ℤ) + 4 + (lam : ℤ) - 1 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 - (-1)) * (m : ℤ) - 2 + (lam : ℤ) - 1) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_false, show (5 : ℕ) ≠ 1 by norm_num]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(1 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_2 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 2)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 2 := by omega
  have hR : Rred m lam r = -(2 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 - 2 * (-1)) * (m : ℤ) + 5 + (lam : ℤ) - 2 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 - 2 * (-1)) * (m : ℤ) - 1 + (lam : ℤ) - 2) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_false, show (5 : ℕ) ≠ 1 by norm_num]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = 1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(2 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_3 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 3)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 3 := by omega
  have hR : Rred m lam r = -(3 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((lam : ℤ) + 3 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ 6 * (m : ℤ) + (lam : ℤ) - 3) := by
    unfold S2 S2bounds
    simp only [hmod]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = -1 := by
    subst hq; unfold epsLam; rw [hmod, if_pos rfl, jacobi_five]
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(3 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_4 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 4)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 4 := by omega
  have hR : Rred m lam r = -(4 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 + 2 * (-1)) * (m : ℤ) + 7 + (lam : ℤ) - 4 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 + 2 * (-1)) * (m : ℤ) + 1 + (lam : ℤ) - 4) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_false, show (5 : ℕ) ≠ 1 by norm_num]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = -1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(4 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

private lemma c16_5_5 (m lam q s r : ℕ) (hq : m = 6 * q + 5) (hs : lam = 6 * s + 5)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have hm6 : m % 6 = 5 := by omega
  have hdiv : lam / 6 = s := by omega
  have hmod : lam % 6 = 5 := by omega
  have hR : Rred m lam r = -(5 * ((q : ℤ) + 1)) + r - s := by
    subst hq
    rw [Rred_eq₂ q _ r (by unfold epsZ; simp [hm6]), hdiv, hmod]; push_cast; ring
  have hS : S2 m lam r ↔ ((3 + (-1)) * (m : ℤ) + 8 + (lam : ℤ) - 5 ≤ 6 * (r : ℤ) ∧
      6 * (r : ℤ) ≤ (9 + (-1)) * (m : ℤ) + 2 + (lam : ℤ) - 5) := by
    unfold S2 S2bounds
    simp only [hmod, hm6, if_false, show (5 : ℕ) ≠ 1 by norm_num]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      first | (qify; linarith) | (qify at h1 h2; linarith)
  have he : epsLam m lam = -1 := by
    unfold epsLam; rw [hmod]; norm_num
  obtain ⟨u, hu, hρ, hb1, hb2⟩ := emod_cases (-(5 * ((q : ℤ) + 1)) + r - s) (2 * m)
    (by omega) (by omega)
  rw [hR, hρ, he]
  simp only [hS]
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [chi] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

/-- The case analysis of the proof of Corollary 1.6. -/
theorem cases_16 (m lam : ℕ) (r : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) (hlam : 0 < lam)
    (h2 : 2 * lam < m) (hr : r < 2 * m) :
    (-1 : ℤ) ^ chi ((m : ℤ) + 1 ≤ 2 * (Rred m lam r % (2 * m)) ∧
        2 * (Rred m lam r % (2 * m)) ≤ 3 * m - 1) =
      (-1) ^ chi (S2 m lam r) * epsLam m lam := by
  have _hm := hm
  have _hlam := hlam
  have hl := (Nat.div_add_mod lam 6).symm
  have ha : lam % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases m_cases m hcop with ⟨q, hq, -, -⟩ | ⟨q, hq, -, -⟩ <;>
  interval_cases h : lam % 6
  · exact c16_1_0 m lam q _ r hq hl h2 hr
  · exact c16_1_1 m lam q _ r hq hl h2 hr
  · exact c16_1_2 m lam q _ r hq hl h2 hr
  · exact c16_1_3 m lam q _ r hq hl h2 hr
  · exact c16_1_4 m lam q _ r hq hl h2 hr
  · exact c16_1_5 m lam q _ r hq hl h2 hr
  · exact c16_5_0 m lam q _ r hq hl h2 hr
  · exact c16_5_1 m lam q _ r hq hl h2 hr
  · exact c16_5_2 m lam q _ r hq hl h2 hr
  · exact c16_5_3 m lam q _ r hq hl h2 hr
  · exact c16_5_4 m lam q _ r hq hl h2 hr
  · exact c16_5_5 m lam q _ r hq hl h2 hr

/-- **Corollary 1.6.** -/
theorem corollary_1_6 (H : ExternalResults) (m lam : ℕ) (hm : 3 < m)
    (hm6 : m % 6 = 1 ∨ m % 6 = 5) (hlam : 0 < lam) (h2 : 2 * lam < m) (r j : ℕ)
    (hr : r ≤ 2 * m - 1) (hj : j ≤ 2) :
    ∀ᶠ n : ℕ in atTop, (n : ℤ) ≡ 3 * r + 2 * m * j [ZMOD 6 * m] →
      Real.sign (coeffGamma m lam n : ℝ) =
        (-1) ^ (r + lam / 6 + chi (S2 m lam r)) * (epsLam m lam : ℝ) := by
  have _hj := hj
  have hcop : Nat.Coprime m 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    rcases hm6 with h | h <;> rw [h] <;> norm_num
  have hm5 : 5 ≤ m := by omega
  have hodd : Odd m := ⟨m / 2, by omega⟩
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
  have hε₀ : 0 < (lam : ℝ) / (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < lam := by exact_mod_cast hlam
    positivity
  have hε : (lam : ℝ) / (m : ℝ) ^ 2 < 1 / (2 * m) := by
    have : 2 * (lam : ℝ) < m := by exact_mod_cast h2
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h16 := congrArg (Int.cast : ℤ → ℝ) (cases_16 m lam r hm5 hcop hlam h2 (by omega))
  push_cast at h16
  filter_upwards [theorem_1_5_sign H m lam hm hcop hlam] with n hn hmod
  rw [hn, Tfun_reduce m lam n r j hm5 hcop hmod,
    show ((r : ℤ) + ((lam / 6 : ℕ) : ℤ)) = ((r + lam / 6 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, sign_neg_one_pow_mul, sign_cos_eps m (by omega) hodd _ _ hε₀ hε, h16, pow_add]
  ring

end ThetaSignPatterns
