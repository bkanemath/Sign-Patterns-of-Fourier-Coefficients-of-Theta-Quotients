import ThetaSignPatterns.Defs

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Dominant cusps (Lemmas 3.2 and 5.2)

Pure real arithmetic: which reduced cusps maximise `A_m(h,k)/k` (resp. `-A_m(h,k)/k`), and a
uniform gap to all other cusps.
-/

open Real

namespace ThetaSignPatterns

/-- `e(j/d)` for an integer `h` with residue `j = h mod d`: `d² (𝔤(h/d) - 𝔤(2h/d)) = 3t² - td`
with `t ∈ {j, d - j}` and `0 ≤ 2t ≤ d`. -/
lemma gfr_diff_eq (h : ℤ) (d : ℕ) (hd : 0 < d) :
    ∃ t : ℤ, (t = h % d ∨ t = d - h % d) ∧ 0 ≤ 2 * t ∧ 2 * t ≤ d ∧
      (d : ℝ) ^ 2 * (gfr ((h : ℝ) / (d : ℝ)) - gfr (2 * (h : ℝ) / (d : ℝ))) =
        3 * (t : ℝ) ^ 2 - t * d := by
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = h % d := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = h / d := ⟨_, rfl⟩
  have hjq : h = d * q + j := by rw [hq, hj]; exact (Int.mul_ediv_add_emod h d).symm
  rw [← hj]
  have hj0 : 0 ≤ j := hj ▸ Int.emod_nonneg _ hdz.ne'
  have hj1 : j < d := hj ▸ Int.emod_lt_of_pos _ hdz
  have hj0r : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hj1r : (j : ℝ) < d := by exact_mod_cast hj1
  have hhr : (h : ℝ) = d * q + j := by exact_mod_cast hjq
  have hf1 : Int.fract ((h : ℝ) / d) = j / d := by
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, by rw [div_lt_one hdr]; exact hj1r, q, ?_⟩
    rw [hhr]; field_simp; ring
  by_cases h2 : 2 * j < d
  · have h2r : (2 * j : ℝ) < d := by exact_mod_cast h2
    have hf2 : Int.fract (2 * (h : ℝ) / d) = 2 * j / d := by
      rw [Int.fract_eq_iff]
      refine ⟨by positivity, by rw [div_lt_one hdr]; exact h2r, 2 * q, ?_⟩
      rw [hhr]; push_cast; field_simp; ring
    refine ⟨j, Or.inl rfl, by omega, by omega, ?_⟩
    unfold gfr; rw [hf1, hf2]; field_simp; ring
  · have h2r : (d : ℝ) ≤ 2 * j := by exact_mod_cast (not_lt.mp h2)
    have hf2 : Int.fract (2 * (h : ℝ) / d) = (2 * j - d) / d := by
      rw [Int.fract_eq_iff]
      refine ⟨div_nonneg (by linarith) hdr.le, by rw [div_lt_one hdr]; linarith, 2 * q + 1, ?_⟩
      rw [hhr]; push_cast; field_simp; ring
    refine ⟨d - j, Or.inr rfl, by omega, by omega, ?_⟩
    unfold gfr; rw [hf1, hf2]; push_cast; field_simp; ring

/-- `A_m(h,k) = π d² e / (m k)` with `d = gcd(m,k)`. -/
lemma Acusp_eq (m : ℕ) (hm : 0 < m) (h : ℤ) (k : ℕ) (hk : 0 < k) (E : ℝ)
    (hE : (Nat.gcd m k : ℝ) ^ 2 * (gfr ((h : ℝ) / (Nat.gcd m k : ℝ)) -
      gfr (2 * (h : ℝ) / (Nat.gcd m k : ℝ))) = E) :
    Acusp m h k = π * E / (m * k) := by
  have hd : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left _ hm
  have hdr : (0 : ℝ) < Nat.gcd m k := by exact_mod_cast hd
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold Acusp
  rw [Nat.cast_div (Nat.gcd_dvd_left m k) hdr.ne', Nat.cast_div (Nat.gcd_dvd_right m k) hdr.ne',
    ← hE]
  field_simp

/-- Residues of `m` coprime to `6`. -/
lemma mod_two_three_of_coprime_six {m d : ℕ} (hcop : Nat.Coprime m 6) (hd : d ∣ m) :
    d % 2 = 1 ∧ d % 3 ≠ 0 := by
  have h2 : ¬ 2 ∣ d := fun h2 => by
    have := Nat.dvd_gcd (h2.trans hd) (by norm_num : 2 ∣ 6)
    rw [Nat.Coprime.gcd_eq_one hcop] at this; norm_num at this
  have h3 : ¬ 3 ∣ d := fun h3 => by
    have := Nat.dvd_gcd (h3.trans hd) (by norm_num : 3 ∣ 6)
    rw [Nat.Coprime.gcd_eq_one hcop] at this; norm_num at this
  omega

lemma epsZ_cases (m : ℕ) (hcop : Nat.Coprime m 6) :
    (epsZ m = 1 ∧ m % 6 = 1) ∨ (epsZ m = -1 ∧ m % 6 = 5) := by
  have := mod_two_three_of_coprime_six hcop dvd_rfl
  unfold epsZ
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, by omega⟩

theorem domOdd_reduced (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∀ p ∈ domOdd m, IsReducedCusp p := by
  have hmo : m % 2 = 1 := Nat.odd_iff.mp hodd
  intro p hp
  simp only [domOdd, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · refine ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨-2, 1, by omega⟩⟩
  · refine ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨2, -1, by omega⟩⟩

/-- **Lemma 3.2** (value). -/
theorem Acusp_domOdd (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (p : ℤ × ℕ) (hp : p ∈ domOdd m) :
    Acusp m p.1 p.2 = p.2 * LamOdd m := by
  have hmo : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hm0 : 0 < m := by omega
  obtain ⟨h, k⟩ := p
  simp only [domOdd, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hp
  have hkm : k = m := by rcases hp with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
  have hh : h = ((m : ℤ) - 1) / 2 ∨ h = ((m : ℤ) + 1) / 2 := by
    rcases hp with ⟨e, _⟩ | ⟨e, _⟩
    · exact Or.inl e
    · exact Or.inr e
  simp only
  rw [hkm]
  obtain ⟨t, ht, ht0, ht1, hE⟩ := gfr_diff_eq h m hm0
  rw [Acusp_eq m hm0 h m hm0 (3 * (t : ℝ) ^ 2 - t * m)
    (by simpa only [Nat.gcd_self] using hE)]
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at ht
  have h2t : 2 * t = (m : ℤ) - 1 := by omega
  have h2tr : 2 * (t : ℝ) = m - 1 := by exact_mod_cast h2t
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [show (t : ℝ) = (m - 1) / 2 by linarith]
  unfold LamOdd
  field_simp
  ring

/-- **Lemma 3.2** (gap). -/
theorem Acusp_le_LamOdd' (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (p : ℤ × ℕ)
    (hp : IsReducedCusp p) (hpD : p ∉ domOdd m) : Acusp m p.1 p.2 ≤ p.2 * LamOdd' m := by
  obtain ⟨h, k⟩ := p
  obtain ⟨h0, hk, -⟩ := hp
  simp only at h0 hk ⊢
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hd0 : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left _ hm0
  obtain ⟨t, ht, ht0, ht1, hE⟩ := gfr_diff_eq h (Nat.gcd m k) hd0
  rw [Acusp_eq m hm0 h k hk0 _ hE]
  have hdk : Nat.gcd m k ∣ k := Nat.gcd_dvd_right m k
  have hdm : Nat.gcd m k ∣ m := Nat.gcd_dvd_left m k
  have hdodd : Nat.gcd m k % 2 = 1 := Nat.odd_iff.mp (hodd.of_dvd_nat hdm)
  generalize Nat.gcd m k = d at hd0 ht ht1 hE hdk hdm hdodd ⊢
  have ht1' : 2 * t ≤ (d : ℤ) - 1 := by omega
  unfold LamOdd'
  set M := max (1 / 4 : ℝ) (((m : ℝ) - 3) * ((m : ℝ) - 9) / (m : ℝ) ^ 2) with hM
  have hM1 : (1 / 4 : ℝ) ≤ M := le_max_left _ _
  have hM2 : ((m : ℝ) - 3) * ((m : ℝ) - 9) / (m : ℝ) ^ 2 ≤ M := le_max_right _ _
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  suffices key : 4 * (3 * (t : ℝ) ^ 2 - t * d) ≤ (k : ℝ) ^ 2 * M by
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) * (π / (4 * m) * M) * (m * k) = π * ((k : ℝ) ^ 2 * M / 4) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) pi_pos.le
  by_cases hkd : k = d
  · by_cases hdm' : d = m
    · -- (iii) `k = d = m`
      have hkm : k = m := hkd.trans hdm'
      have hdmz : (d : ℤ) = m := by exact_mod_cast hdm'
      rw [hdmz, Int.emod_eq_of_lt h0
        (by rw [← hdmz, show (d : ℤ) = k by exact_mod_cast hkd.symm]; exact hk)] at ht
      have hne : h ≠ ((m : ℤ) - 1) / 2 ∧ h ≠ ((m : ℤ) + 1) / 2 := by
        simp only [domOdd, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, not_or] at hpD
        exact ⟨fun e => hpD.1 ⟨e, hkm⟩, fun e => hpD.2 ⟨e, hkm⟩⟩
      have hmodd : m % 2 = 1 := Nat.odd_iff.mp hodd
      have ht2 : 2 * t ≤ (m : ℤ) - 3 := by omega
      have hint : 4 * (3 * t ^ 2 - t * m) ≤ 0 ∨
          4 * (3 * t ^ 2 - t * m) ≤ ((m : ℤ) - 3) * ((m : ℤ) - 9) := by
        by_cases hc : 0 ≤ 6 * t + m - 9
        · right; nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ m - 3 - 2 * t) hc]
        · left
          nlinarith [mul_nonneg (show 0 ≤ t by omega) (show (0 : ℤ) ≤ m - 3 * t by omega)]
      rw [show (d : ℝ) = m by exact_mod_cast hdm', show (k : ℝ) = m by exact_mod_cast hkm]
      rcases hint with hint | hint
      · have : 4 * (3 * (t : ℝ) ^ 2 - t * m) ≤ 0 := by exact_mod_cast hint
        nlinarith [sq_nonneg (m : ℝ)]
      · have h1 : 4 * (3 * (t : ℝ) ^ 2 - t * m) ≤ ((m : ℝ) - 3) * ((m : ℝ) - 9) := by
          exact_mod_cast hint
        have h2 : (m : ℝ) ^ 2 * (((m : ℝ) - 3) * ((m : ℝ) - 9) / (m : ℝ) ^ 2) =
            ((m : ℝ) - 3) * ((m : ℝ) - 9) := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hM2 (sq_nonneg (m : ℝ))]
    · -- (ii) `k = d < m`, so `3d ≤ m`
      obtain ⟨μ, hμ⟩ := hdm
      have hμodd : μ % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (hμ ▸ hodd)).2
      have hμ1 : μ ≠ 1 := fun e => hdm' (by rw [hμ, e, mul_one])
      have hμ3 : 3 ≤ μ := by omega
      have h3d : 3 * d ≤ m := by rw [hμ]; nlinarith
      rw [show (k : ℝ) = d by exact_mod_cast hkd]
      by_cases hd1 : d = 1
      · have : t = 0 := by subst hd1; push_cast at ht1'; omega
        rw [this, hd1]; push_cast; nlinarith
      · have hd3 : 3 ≤ d := by omega
        have hint : 4 * (3 * t ^ 2 - t * d) ≤ ((d : ℤ) - 1) * ((d : ℤ) - 3) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ d - 1 - 2 * t)
            (by omega : (0 : ℤ) ≤ 6 * t + d - 3)]
        have hintr : 4 * (3 * (t : ℝ) ^ 2 - t * d) ≤ ((d : ℝ) - 1) * ((d : ℝ) - 3) := by
          exact_mod_cast hint
        have hd3r : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        have h3dr : 3 * (d : ℝ) ≤ m := by exact_mod_cast h3d
        have hX : ((d : ℝ) - 1) * ((d : ℝ) - 3) ≤
            (d : ℝ) ^ 2 * (((m : ℝ) - 3) * ((m : ℝ) - 9) / (m : ℝ) ^ 2) := by
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - 3 * d)
            (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d - 3) hmr.le] :
              (0 : ℝ) ≤ 4 * d * m - 3 * m - 9 * d)]
        nlinarith [mul_le_mul_of_nonneg_left hM2 (sq_nonneg (d : ℝ))]
  · -- (i) `k ≠ d`, so `2d ≤ k`
    obtain ⟨κ, hκ⟩ := hdk
    have hκ0 : κ ≠ 0 := fun e => by rw [e, mul_zero] at hκ; omega
    have hκ1 : κ ≠ 1 := fun e => hkd (by rw [hκ, e, mul_one])
    have h2d : 2 * (d : ℝ) ≤ k := by
      exact_mod_cast (show 2 * d ≤ k by rw [hκ]; nlinarith [show 2 ≤ κ by omega])
    have hint : 4 * (3 * (t : ℝ) ^ 2 - t * d) ≤ (d : ℝ) ^ 2 := by
      have : 4 * (3 * t ^ 2 - t * (d : ℤ)) ≤ (d : ℤ) ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ 6 * t + d by omega)
          (show (0 : ℤ) ≤ d - 2 * t by omega)]
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_left hM1 (sq_nonneg (k : ℝ))]

theorem LamOdd'_lt (m : ℕ) (hm : 5 ≤ m) : LamOdd' m < LamOdd m := by
  have hmr : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hL : LamOdd m = π / (4 * m) * (((m : ℝ) - 1) * ((m : ℝ) - 3) / (m : ℝ) ^ 2) := by
    unfold LamOdd; field_simp
  rw [hL]
  unfold LamOdd'
  refine mul_lt_mul_of_pos_left (max_lt ?_ ?_) (by positivity)
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · exact div_lt_div_of_pos_right (by nlinarith) (by positivity)

theorem domT_reduced (m : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) :
    ∀ p ∈ domT m, IsReducedCusp p := by
  intro p hp
  simp only [domT, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases epsZ_cases m hcop with ⟨he, hm6⟩ | ⟨he, hm6⟩ <;> rw [he] at hp <;>
    rcases hp with rfl | rfl
  · exact ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨-6, 1, by omega⟩⟩
  · exact ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨6, -5, by omega⟩⟩
  · exact ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨6, -1, by omega⟩⟩
  · exact ⟨by omega, by omega, Int.isCoprime_iff_gcd_eq_one.mp ⟨-6, 5, by omega⟩⟩

/-- **Lemma 5.2** (value). -/
theorem Acusp_domT (m : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) (p : ℤ × ℕ)
    (hp : p ∈ domT m) : -Acusp m p.1 p.2 = p.2 * LamT m := by
  have hm0 : 0 < m := by omega
  obtain ⟨h, k⟩ := p
  simp only [domT, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hp
  have hkm : k = m := by rcases hp with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
  have hh : h = ((m : ℤ) - epsZ m) / 6 ∨ h = (5 * (m : ℤ) + epsZ m) / 6 := by
    rcases hp with ⟨e, _⟩ | ⟨e, _⟩
    · exact Or.inl e
    · exact Or.inr e
  simp only
  rw [hkm]
  obtain ⟨t, ht, ht0, ht1, hE⟩ := gfr_diff_eq h m hm0
  rw [Acusp_eq m hm0 h m hm0 (3 * (t : ℝ) ^ 2 - t * m)
    (by simpa only [Nat.gcd_self] using hE)]
  have hε := epsZ_cases m hcop
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at ht
  have h6 : 6 * t - m = 1 ∨ 6 * t - m = -1 := by omega
  have hsq : (6 * (t : ℝ) - m) ^ 2 = 1 := by
    rcases h6 with e | e
    · have : 6 * (t : ℝ) - m = 1 := by exact_mod_cast e
      rw [this]; norm_num
    · have : 6 * (t : ℝ) - m = -1 := by exact_mod_cast e
      rw [this]; norm_num
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have key : 12 * ((t : ℝ) * m - 3 * t ^ 2) = (m : ℝ) ^ 2 - 1 := by
    linear_combination (-1 : ℝ) * hsq
  rw [show -(π * (3 * (t : ℝ) ^ 2 - t * m) / (m * m)) =
    π * (12 * ((t : ℝ) * m - 3 * t ^ 2)) / (12 * m * m) by ring, key]
  unfold LamT
  field_simp

/-- **Lemma 5.2** (gap). -/
theorem neg_Acusp_le_LamT' (m : ℕ) (hm : 5 ≤ m) (hcop : Nat.Coprime m 6) (p : ℤ × ℕ)
    (hp : IsReducedCusp p) (hpD : p ∉ domT m) : -Acusp m p.1 p.2 ≤ p.2 * LamT' m := by
  obtain ⟨h, k⟩ := p
  obtain ⟨h0, hk, -⟩ := hp
  simp only at h0 hk ⊢
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hd0 : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left _ hm0
  obtain ⟨t, ht, ht0, ht1, hE⟩ := gfr_diff_eq h (Nat.gcd m k) hd0
  rw [Acusp_eq m hm0 h k hk0 _ hE]
  have hdk : Nat.gcd m k ∣ k := Nat.gcd_dvd_right m k
  have hdm : Nat.gcd m k ∣ m := Nat.gcd_dvd_left m k
  have hd6 := mod_two_three_of_coprime_six hcop hdm
  generalize Nat.gcd m k = d at hd0 ht ht1 hE hdk hdm hd6 ⊢
  unfold LamT'
  set M := max (1 / 4 : ℝ) (((m : ℝ) ^ 2 - 25) / (m : ℝ) ^ 2) with hM
  have hM1 : (1 / 4 : ℝ) ≤ M := le_max_left _ _
  have hM2 : ((m : ℝ) ^ 2 - 25) / (m : ℝ) ^ 2 ≤ M := le_max_right _ _
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have h6 : 6 * t - d ≠ 0 := by omega
  suffices key : 12 * ((t : ℝ) * d - 3 * t ^ 2) ≤ (k : ℝ) ^ 2 * M by
    rw [show -(π * (3 * (t : ℝ) ^ 2 - t * d) / (m * k)) =
      π * ((t : ℝ) * d - 3 * t ^ 2) / (m * k) by ring, div_le_iff₀ (by positivity)]
    have : (k : ℝ) * (π / (12 * m) * M) * (m * k) = π * ((k : ℝ) ^ 2 * M / 12) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) pi_pos.le
  -- `12 (t d - 3 t²) = d² - (6t - d)²`
  have hid : 12 * ((t : ℝ) * d - 3 * t ^ 2) = (d : ℝ) ^ 2 - (6 * t - d) ^ 2 := by ring
  rw [hid]
  by_cases hkd : k = d
  · have hsq1 : (1 : ℝ) ≤ (6 * t - d) ^ 2 := by
      have : (1 : ℤ) ≤ (6 * t - d) ^ 2 := by
        rcases lt_or_gt_of_ne h6 with h' | h' <;> nlinarith
      exact_mod_cast this
    by_cases hdm' : d = m
    · -- (iii) `k = d = m`
      have hkm : k = m := hkd.trans hdm'
      have hdmz : (d : ℤ) = m := by exact_mod_cast hdm'
      rw [hdmz, Int.emod_eq_of_lt h0
        (by rw [← hdmz, show (d : ℤ) = k by exact_mod_cast hkd.symm]; exact hk)] at ht
      have hne : h ≠ ((m : ℤ) - epsZ m) / 6 ∧ h ≠ (5 * (m : ℤ) + epsZ m) / 6 := by
        simp only [domT, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, not_or] at hpD
        exact ⟨fun e => hpD.1 ⟨e, hkm⟩, fun e => hpD.2 ⟨e, hkm⟩⟩
      have hε := epsZ_cases m hcop
      have h5 : 5 ≤ 6 * t - m ∨ 6 * t - m ≤ -5 := by omega
      have hsq : (25 : ℝ) ≤ (6 * t - m) ^ 2 := by
        have : (25 : ℤ) ≤ (6 * t - m) ^ 2 := by rcases h5 with h' | h' <;> nlinarith
        exact_mod_cast this
      rw [show (d : ℝ) = m by exact_mod_cast hdm', show (k : ℝ) = m by exact_mod_cast hkm]
      have h2 : (m : ℝ) ^ 2 * (((m : ℝ) ^ 2 - 25) / (m : ℝ) ^ 2) = (m : ℝ) ^ 2 - 25 := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hM2 (sq_nonneg (m : ℝ))]
    · -- (ii) `k = d < m`, so `5d ≤ m`
      obtain ⟨μ, hμ⟩ := hdm
      have hμ6 := mod_two_three_of_coprime_six hcop (Dvd.intro_left d hμ.symm)
      have hμ1 : μ ≠ 1 := fun e => hdm' (by rw [hμ, e, mul_one])
      have hμ5 : 5 ≤ μ := by omega
      have h5d : 5 * d ≤ m := by rw [hμ]; nlinarith
      have h5dr : 5 * (d : ℝ) ≤ m := by exact_mod_cast h5d
      rw [show (k : ℝ) = d by exact_mod_cast hkd]
      have hX : (d : ℝ) ^ 2 - 1 ≤ (d : ℝ) ^ 2 * (((m : ℝ) ^ 2 - 25) / (m : ℝ) ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul h5dr h5dr (by positivity) hmr.le]
      nlinarith [mul_le_mul_of_nonneg_left hM2 (sq_nonneg (d : ℝ))]
  · -- (i) `k ≠ d`, so `2d ≤ k`
    obtain ⟨κ, hκ⟩ := hdk
    have hκ0 : κ ≠ 0 := fun e => by rw [e, mul_zero] at hκ; omega
    have hκ1 : κ ≠ 1 := fun e => hkd (by rw [hκ, e, mul_one])
    have h2d : 2 * (d : ℝ) ≤ k := by
      exact_mod_cast (show 2 * d ≤ k by rw [hκ]; nlinarith [show 2 ≤ κ by omega])
    nlinarith [mul_le_mul_of_nonneg_left hM1 (sq_nonneg (k : ℝ)), sq_nonneg (6 * (t : ℝ) - d)]

theorem LamT'_lt (m : ℕ) (hm : 5 ≤ m) : LamT' m < LamT m := by
  have hmr : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hL : LamT m = π / (12 * m) * (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) := by
    unfold LamT; field_simp
  rw [hL]
  unfold LamT'
  refine mul_lt_mul_of_pos_left (max_lt ?_ ?_) (by positivity)
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · exact div_lt_div_of_pos_right (by linarith) (by positivity)

end ThetaSignPatterns
