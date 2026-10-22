import ThetaSignPatterns.ThetaProduct

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Modularity of `f_{m,𝓁}` and `f̃_{m,λ}`

Quotients of weight-`1/2` forms, powers, and level raising `τ ↦ g(Nτ)` (all proved), applied
to the theta functions of E2.5.
-/

open Complex Filter Topology Real

namespace ThetaSignPatterns

open Matrix CongruenceSubgroup
open scoped MatrixGroups

/-- `cτ + d ≠ 0` on the upper half-plane. -/
lemma jfac_ne_zero (γ : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) : jfac γ τ ≠ 0 := by
  intro h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have him : ((γ 1 0 : ℤ) : ℝ) * τ.im = 0 := by simpa [jfac] using congrArg Complex.im h
  have hc : γ 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact_mod_cast h1
    · linarith
  have hd : γ 1 1 = 0 := by
    have : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa [jfac, hc] using congrArg Complex.re h
    exact_mod_cast this
  rw [hc, hd] at hdet
  simp at hdet

theorem isWHModular_quot (g₁ g₂ : ℂ → ℂ) (h₁ : IsWHModular (1 / 2) g₁)
    (h₂ : IsWHModular (1 / 2) g₂) (h₂l : HasCuspLowerBound (1 / 2) g₂)
    (h₂ne : ∀ τ : ℂ, 0 < τ.im → g₂ τ ≠ 0) (ℓ : ℕ) :
    IsWHModular 0 (fun τ => (g₁ τ / g₂ τ) ^ ℓ) := by
  obtain ⟨hd₁, Γ₁, hΓ₁, χ₁, hχ₁, hinv₁, hcusp₁⟩ := h₁
  obtain ⟨hd₂, Γ₂, hΓ₂, χ₂, hχ₂, hinv₂, -⟩ := h₂
  refine ⟨(hd₁.div hd₂ fun τ hτ => h₂ne τ hτ).pow ℓ, Γ₁ ⊓ Γ₂, inferInstance,
    fun γ => (χ₁ γ / χ₂ γ) ^ ℓ, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hγ₁, hγ₂⟩ := Subgroup.mem_inf.mp hγ
    simp [hχ₁ γ hγ₁, hχ₂ γ hγ₂]
  · intro γ hγ τ hτ
    obtain ⟨hγ₁, hγ₂⟩ := Subgroup.mem_inf.mp hγ
    have hχne : χ₂ γ ≠ 0 := by
      intro h; have := hχ₂ γ hγ₂; simp [h] at this
    have hJ : jfac γ τ ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => jfac_ne_zero γ hτ h.1
    have hg := h₂ne τ hτ
    simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one]
    rw [hinv₁ γ hγ₁ τ hτ, hinv₂ γ hγ₂ τ hτ, ← mul_pow]
    congr 1
    field_simp
  · intro γ
    obtain ⟨A₁, C₁, T₁, hb₁⟩ := hcusp₁ γ
    obtain ⟨A₂, c₂, T₂, hc₂, hb₂⟩ := h₂l γ
    refine ⟨ℓ * (A₁ + A₂), (C₁ / c₂) ^ ℓ, max (max T₁ T₂) 1, fun τ hτ => ?_⟩
    have hτ1 : T₁ ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
    have hτ2 : T₂ ≤ τ.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
    have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hτ)
    have hJ : jfac γ τ ^ (-(((1 / 2 : ℝ)) : ℂ)) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => jfac_ne_zero γ hτ0 h.1
    have e1 := hb₁ τ hτ1
    have e2 := hb₂ τ hτ2
    have hq : g₁ (mob γ τ) / g₂ (mob γ τ) =
        (jfac γ τ ^ (-(((1 / 2 : ℝ)) : ℂ)) * g₁ (mob γ τ)) /
          (jfac γ τ ^ (-(((1 / 2 : ℝ)) : ℂ)) * g₂ (mob γ τ)) := by
      rw [mul_div_mul_left _ _ hJ]
    simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_mul]
    rw [hq, norm_pow, norm_div]
    have hv : 0 < c₂ * Real.exp (-(A₂ * τ.im)) := by positivity
    have hC : 0 ≤ C₁ * Real.exp (A₁ * τ.im) := le_trans (norm_nonneg _) e1
    have key : C₁ * Real.exp (A₁ * τ.im) / (c₂ * Real.exp (-(A₂ * τ.im))) =
        C₁ / c₂ * Real.exp ((A₁ + A₂) * τ.im) := by
      rw [mul_div_mul_comm, ← Real.exp_sub]; ring_nf
    calc _ ≤ (C₁ * Real.exp (A₁ * τ.im) / (c₂ * Real.exp (-(A₂ * τ.im)))) ^ ℓ :=
          pow_le_pow_left₀ (by positivity) (div_le_div₀ hC e1 hv e2) ℓ
      _ = (C₁ / c₂) ^ ℓ * Real.exp (ℓ * (A₁ + A₂) * τ.im) := by
          rw [key, mul_pow, ← Real.exp_nat_mul]; ring_nf

/-! ### Level raising -/

lemma dvd_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 N) : (N : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h)

/-- The matrix `[[a, N b], [c / N, d]]`. -/
def psiMat (N : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, N * γ 0 1; γ 1 0 / N, γ 1 1]

/-- The conjugation `[[a, b], [c, d]] ↦ [[a, N b], [c / N, d]]`, a homomorphism
`Γ₀(N) → SL₂(ℤ)` (conjugation by `diag(N, 1)`). -/
noncomputable def psi (N : ℕ) (hN : 0 < N) : Gamma0 N →* SL(2, ℤ) where
  toFun γ := ⟨psiMat N γ, by
    obtain ⟨k, hk⟩ := dvd_of_mem_Gamma0 γ.2
    have hN0 : (N : ℤ) ≠ 0 := by positivity
    have hdet := (γ : SL(2, ℤ)).det_coe
    rw [Matrix.det_fin_two, hk] at hdet
    rw [psiMat, Matrix.det_fin_two_of, hk, Int.mul_ediv_cancel_left _ hN0]
    linear_combination hdet⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [psiMat]
  map_mul' γ δ := by
    obtain ⟨k₁, hk₁⟩ := dvd_of_mem_Gamma0 γ.2
    obtain ⟨k₂, hk₂⟩ := dvd_of_mem_Gamma0 δ.2
    have hN0 : (N : ℤ) ≠ 0 := by positivity
    apply Subtype.ext
    show psiMat N ((γ * δ : Gamma0 N) : SL(2, ℤ)) = psiMat N γ * psiMat N δ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [psiMat, Matrix.mul_apply, Fin.sum_univ_two, hk₁, hk₂,
        Int.mul_ediv_cancel_left _ hN0, Matrix.SpecialLinearGroup.coe_mul] <;>
      first | ring1 | (rw [Int.ediv_eq_of_eq_mul_right hN0]; ring)

lemma psi_apply (N : ℕ) (hN : 0 < N) (γ : Gamma0 N) (i j : Fin 2) :
    (psi N hN γ : SL(2, ℤ)) i j = psiMat N γ i j := rfl

/-- `N · γτ = ψ(γ)(Nτ)`. -/
lemma natCast_mul_mob (N : ℕ) (hN : 0 < N) (γ : Gamma0 N) (τ : ℂ) :
    (N : ℂ) * mob γ τ = mob (psi N hN γ) (N * τ) := by
  obtain ⟨k, hk⟩ := dvd_of_mem_Gamma0 γ.2
  have hN0 : (N : ℤ) ≠ 0 := by positivity
  simp only [mob, psi_apply, psiMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hk,
    Int.mul_ediv_cancel_left _ hN0]
  push_cast
  rw [← mul_div_assoc]
  congr 1 <;> ring

/-- Integer Hermite step: `diag(N,1) γ = γ'' [[a', b'], [0, d']]` with `γ'' ∈ SL₂(ℤ)`. -/
lemma hermite_aux (N a b c d : ℤ) (hN : 0 < N) (hdet : a * d - b * c = 1) :
    ∃ p q r s a' b' d' : ℤ, p * s - q * r = 1 ∧ 0 < a' ∧ 0 < d' ∧ p * a' = N * a ∧
      p * b' + q * d' = N * b ∧ r * a' = c ∧ r * b' + s * d' = d := by
  set g : ℤ := (Int.gcd (N * a) c : ℤ) with hg
  have hg0 : g ≠ 0 := by
    rw [hg, Nat.cast_ne_zero, Ne, Int.gcd_eq_zero_iff]
    rintro ⟨h1, h2⟩
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · omega
      · exact h
    rw [ha, h2] at hdet; simp at hdet
  have hgpos : 0 < g := lt_of_le_of_ne (by positivity) (Ne.symm hg0)
  obtain ⟨p, hp⟩ : g ∣ N * a := Int.gcd_dvd_left _ _
  obtain ⟨r, hr⟩ : g ∣ c := Int.gcd_dvd_right _ _
  have hbez : g = N * a * Int.gcdA (N * a) c + c * Int.gcdB (N * a) c := Int.gcd_eq_gcd_ab _ _
  have h1 : p * Int.gcdA (N * a) c - (-Int.gcdB (N * a) c) * r = 1 := by
    have : g * (p * Int.gcdA (N * a) c - (-Int.gcdB (N * a) c) * r) = g * 1 := by
      linear_combination (-(Int.gcdA (N * a) c)) * hp - Int.gcdB (N * a) c * hr - hbez
    exact mul_left_cancel₀ hg0 this
  have hd' : g * (p * d - r * N * b) = N := by
    linear_combination (-d) * hp + (N * b) * hr + N * hdet
  refine ⟨p, -Int.gcdB (N * a) c, r, Int.gcdA (N * a) c, g,
    Int.gcdA (N * a) c * N * b - (-Int.gcdB (N * a) c) * d, p * d - r * N * b,
    h1, hgpos, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hneg
    push Not at hneg
    nlinarith
  · linear_combination -hp
  · linear_combination (N * b) * h1
  · linear_combination -hr
  · linear_combination d * h1

/-- For every `γ`, `N · γτ = γ''((a'τ + b')/d')` with `γ'' ∈ SL₂(ℤ)`, `a', d' > 0`. -/
lemma exists_natCast_mul_mob (N : ℕ) (hN : 0 < N) (γ : SL(2, ℤ)) :
    ∃ (γ'' : SL(2, ℤ)) (a' b' d' : ℤ), 0 < a' ∧ 0 < d' ∧
      ∀ τ : ℂ, 0 < τ.im → (N : ℂ) * mob γ τ = mob γ'' ((a' * τ + b') / d') := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  obtain ⟨p, q, r, s, a', b', d', h1, ha', hd', e1, e2, e3, e4⟩ :=
    hermite_aux N (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (by exact_mod_cast hN) hdet
  let γ'' : SL(2, ℤ) := ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h1⟩
  refine ⟨γ'', a', b', d', ha', hd', fun τ hτ => ?_⟩
  have hj := jfac_ne_zero γ hτ
  simp only [jfac] at hj
  have hd0 : (d' : ℂ) ≠ 0 := by exact_mod_cast hd'.ne'
  have c1 : (p : ℂ) * a' = N * γ 0 0 := by exact_mod_cast e1
  have c2 : (p : ℂ) * b' + q * d' = N * γ 0 1 := by exact_mod_cast e2
  have c3 : (r : ℂ) * a' = γ 1 0 := by exact_mod_cast e3
  have c4 : (r : ℂ) * b' + s * d' = γ 1 1 := by exact_mod_cast e4
  have hnum : (p : ℂ) * ((a' * τ + b') / d') + q = (N * γ 0 0 * τ + N * γ 0 1) / d' := by
    field_simp
    linear_combination τ * c1 + c2
  have hden : (r : ℂ) * ((a' * τ + b') / d') + s = (γ 1 0 * τ + γ 1 1) / d' := by
    field_simp
    linear_combination τ * c3 + c4
  have hmob : mob γ'' ((a' * τ + b') / d') =
      ((p : ℂ) * ((a' * τ + b') / d') + q) / ((r : ℂ) * ((a' * τ + b') / d') + s) := rfl
  rw [hmob, hnum, hden, div_div_div_cancel_right₀ hd0, mob, ← mul_div_assoc]
  congr 1; ring

theorem isWHModular_comp_mul (g : ℂ → ℂ) (hg : IsWHModular 0 g) (N : ℕ) (hN : 0 < N) :
    IsWHModular 0 (fun τ => g (N * τ)) := by
  classical
  obtain ⟨hd, Γ, hΓ, χ, hχ, hinv, hcusp⟩ := hg
  have hNim : ∀ τ : ℂ, 0 < τ.im → 0 < ((N : ℂ) * τ).im := fun τ hτ => by
    simpa using mul_pos (Nat.cast_pos.mpr hN) hτ
  let χ' : SL(2, ℤ) → ℂ := fun γ => if h : γ ∈ Gamma0 N then χ (psi N hN ⟨γ, h⟩) else 1
  have hχ' : ∀ x : Gamma0 N, χ' x = χ (psi N hN x) := fun x => dif_pos x.2
  have : NeZero N := ⟨hN.ne'⟩
  have : (Γ.comap (psi N hN)).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_comap]
    exact @Subgroup.relIndex_ne_zero _ _ _ _ Subgroup.isFiniteRelIndex_of_finiteIndex
  refine ⟨hd.comp (by fun_prop) (fun τ hτ => hNim τ hτ),
    (Γ.comap (psi N hN)).map (Gamma0 N).subtype, ?_, χ', ?_, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff, Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  · intro γ hγ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hγ
    rw [Subgroup.coe_subtype, hχ' x]
    exact hχ _ (Subgroup.mem_comap.mp hx)
  · intro γ hγ τ hτ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hγ
    simp only [Subgroup.coe_subtype, Complex.ofReal_zero, Complex.cpow_zero, mul_one]
    rw [natCast_mul_mob N hN x, hinv _ (Subgroup.mem_comap.mp hx) _ (hNim τ hτ), hχ' x]
    simp
  · intro γ
    obtain ⟨γ'', a', b', d', ha', hd', hmob⟩ := exists_natCast_mul_mob N hN γ
    obtain ⟨A, C, T, hT⟩ := hcusp γ''
    have ha'R : (0 : ℝ) < a' := by exact_mod_cast ha'
    have hd'R : (0 : ℝ) < d' := by exact_mod_cast hd'
    refine ⟨A * a' / d', C, max (T * d' / a') 1, fun τ hτ => ?_⟩
    have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hτ)
    have him : (((a' : ℂ) * τ + b') / (d' : ℂ)).im = a' / d' * τ.im := by
      rw [Complex.div_intCast_im]; simp; ring
    have hT' : T ≤ (((a' : ℂ) * τ + b') / (d' : ℂ)).im := by
      have h1 : T * d' / a' ≤ τ.im := le_trans (le_max_left _ _) hτ
      rw [div_le_iff₀ ha'R] at h1
      rw [him, div_mul_eq_mul_div, le_div_iff₀ hd'R]
      linarith
    have key := hT _ hT'
    simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_mul] at key ⊢
    rw [hmob τ hτ0]
    rw [him] at key
    convert key using 3
    ring

/-! ### The functions `f_{m,𝓁}` and `f̃_{m,λ}` -/

lemma not_int_div (m j : ℕ) (hj0 : 0 < j) (hjm : j < m) : ∀ n : ℤ, (j : ℚ) / m ≠ n := by
  intro n h
  have hm : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 : (0 : ℚ) < n := by rw [← h]; positivity
  have h2 : (n : ℚ) < 1 := by rw [← h, div_lt_one hm]; exact_mod_cast hjm
  have h3 : (0 : ℤ) < n := by exact_mod_cast h1
  have h4 : n < 1 := by exact_mod_cast h2
  omega

/-- `Θ_{1/m}` and `Θ_{2/m}` do not vanish on `ℍ`. -/
lemma thetaRat_ne_zero (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) (τ : ℂ) (hτ : 0 < τ.im) :
    thetaRat (1 / (m : ℚ)) τ ≠ 0 ∧ thetaRat (2 / (m : ℚ)) τ ≠ 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hw : 0 < (τ / m).im := by
    rw [Complex.div_natCast_im]; exact div_pos hτ (by exact_mod_cast (by omega : 0 < m))
  obtain ⟨h1, h2⟩ :=
    theta_ne_zero_of H m hm (τ / m) τ hw ⟨0, by rw [mul_div_cancel₀ _ hm0]; simp⟩
  refine ⟨mul_ne_zero (Complex.exp_ne_zero _) ?_, mul_ne_zero (Complex.exp_ne_zero _) ?_⟩
  · convert h1 using 2; push_cast; ring
  · convert h2 using 2; push_cast; ring

lemma thetaRat_modular (H : ExternalResults) (m : ℕ) (hm : 3 ≤ m) :
    (IsWHModular (1 / 2) (thetaRat (1 / (m : ℚ))) ∧
      HasCuspLowerBound (1 / 2) (thetaRat (1 / (m : ℚ)))) ∧
    (IsWHModular (1 / 2) (thetaRat (2 / (m : ℚ))) ∧
      HasCuspLowerBound (1 / 2) (thetaRat (2 / (m : ℚ)))) :=
  ⟨H.thetaModular _ (by simpa using not_int_div m 1 one_pos (by omega)),
    H.thetaModular _ (by simpa using not_int_div m 2 two_pos (by omega))⟩

/-- `Θ_{j/m}(mτ) = e^{πij²τ/m} ϑ(jτ; mτ)` for `j = 1, 2`. -/
lemma thetaRat_natCast_mul (m : ℕ) (hm : 3 ≤ m) (τ : ℂ) :
    thetaRat (1 / (m : ℚ)) (m * τ) = cexp (π * I * τ / m) * theta τ (m * τ) ∧
    thetaRat (2 / (m : ℚ)) (m * τ) = cexp (4 * π * I * τ / m) * theta (2 * τ) (m * τ) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  constructor
  · rw [thetaRat]; push_cast
    congr 2
    · field_simp
    · field_simp
  · rw [thetaRat]; push_cast
    congr 2
    · field_simp; ring
    · field_simp

theorem fMod_isWHModular (H : ExternalResults) (m ℓ : ℕ) (hm : 3 ≤ m) :
    IsWHModular 0 (fMod m ℓ) := by
  obtain ⟨⟨h1, -⟩, ⟨h2, h2l⟩⟩ := thetaRat_modular H m hm
  have hQ := isWHModular_quot _ _ h1 h2 h2l (fun τ hτ => (thetaRat_ne_zero H m hm τ hτ).2) ℓ
  have heq : fMod m ℓ = fun τ =>
      (fun τ' => (thetaRat (1 / (m : ℚ)) τ' / thetaRat (2 / (m : ℚ)) τ') ^ ℓ) (m * τ) := by
    funext τ
    obtain ⟨e1, e2⟩ := thetaRat_natCast_mul m hm τ
    simp only [fMod, e1, e2]
  rw [heq]
  exact isWHModular_comp_mul _ hQ m (by omega)

theorem fModT_isWHModular (H : ExternalResults) (m lam : ℕ) (hm : 3 ≤ m) :
    IsWHModular 0 (fModT m lam) := by
  obtain ⟨⟨h1, h1l⟩, ⟨h2, -⟩⟩ := thetaRat_modular H m hm
  have hQ := isWHModular_quot _ _ h2 h1 h1l (fun τ hτ => (thetaRat_ne_zero H m hm τ hτ).1) lam
  have heq : fModT m lam = fun τ =>
      (fun τ' => (thetaRat (2 / (m : ℚ)) τ' / thetaRat (1 / (m : ℚ)) τ') ^ lam) (m * τ) := by
    funext τ
    obtain ⟨e1, e2⟩ := thetaRat_natCast_mul m hm τ
    simp only [fModT, e1, e2]
  rw [heq]
  exact isWHModular_comp_mul _ hQ m (by omega)

end ThetaSignPatterns
