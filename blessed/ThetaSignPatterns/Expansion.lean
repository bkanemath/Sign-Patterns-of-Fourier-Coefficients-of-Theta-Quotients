import ThetaSignPatterns.Formal

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# The infinite products and their power series

For `|q| < 1` the products `F_m(q)` and `F̃_m(q)` converge, are nonzero, are inverse to each
other, and `∑ c^{[𝓁]}_m(n) qⁿ = F_m(q)^𝓁`, `∑ γ^{[λ]}_m(n) qⁿ = F̃_m(q)^λ`.
-/

open Complex Filter Topology

namespace ThetaSignPatterns


/-! ### Power series with integer coefficients converging on the unit disc -/

/-- `f q = ∑ Aₙ qⁿ` on the unit disc, absolutely. -/
def HasCoeffs (f : ℂ → ℂ) (A : PowerSeries ℤ) : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => ‖((PowerSeries.coeff n A : ℤ) : ℂ) * q ^ n‖) ∧
    HasSum (fun n => ((PowerSeries.coeff n A : ℤ) : ℂ) * q ^ n) (f q)

lemma HasCoeffs.congr {f g : ℂ → ℂ} {A : PowerSeries ℤ} (h : HasCoeffs f A)
    (hfg : ∀ q, ‖q‖ < 1 → f q = g q) : HasCoeffs g A := fun q hq =>
  ⟨(h q hq).1, hfg q hq ▸ (h q hq).2⟩

lemma hasCoeffs_one : HasCoeffs (fun _ => 1) 1 := by
  intro q _
  have h : (fun n => ((PowerSeries.coeff n (1 : PowerSeries ℤ) : ℤ) : ℂ) * q ^ n) =
      fun n => if n = 0 then (1 : ℂ) else 0 := by
    funext n
    rw [PowerSeries.coeff_one]
    split_ifs with hn <;> simp [hn]
  rw [h]
  refine ⟨summable_of_ne_finset_zero (s := {0}) ?_, hasSum_ite_eq 0 1⟩
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [hn]

lemma HasCoeffs.mul {f g : ℂ → ℂ} {A B : PowerSeries ℤ} (hf : HasCoeffs f A)
    (hg : HasCoeffs g B) : HasCoeffs (fun q => f q * g q) (A * B) := by
  intro q hq
  obtain ⟨hsA, hA⟩ := hf q hq
  obtain ⟨hsB, hB⟩ := hg q hq
  have key : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((PowerSeries.coeff kl.1 A : ℤ) : ℂ) * q ^ kl.1 *
        (((PowerSeries.coeff kl.2 B : ℤ) : ℂ) * q ^ kl.2) =
      ((PowerSeries.coeff n (A * B) : ℤ) : ℂ) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsA hsB
  have ht := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsA hsB
  simp only [key] at hs ht
  refine ⟨hs, ?_⟩
  have := hs.of_norm.hasSum
  rwa [← ht, hA.tsum_eq, hB.tsum_eq] at this

lemma HasCoeffs.pow {f : ℂ → ℂ} {A : PowerSeries ℤ} (hf : HasCoeffs f A) (ℓ : ℕ) :
    HasCoeffs (fun q => f q ^ ℓ) (A ^ ℓ) := by
  induction ℓ with
  | zero => simpa using hasCoeffs_one
  | succ ℓ ih => simpa [pow_succ] using ih.mul hf

lemma HasCoeffs.prod_range {f : ℕ → ℂ → ℂ} {A : ℕ → PowerSeries ℤ}
    (hf : ∀ j, HasCoeffs (f j) (A j)) (N : ℕ) :
    HasCoeffs (fun q => ∏ j ∈ Finset.range N, f j q) (∏ j ∈ Finset.range N, A j) := by
  induction N with
  | zero => simpa using hasCoeffs_one
  | succ N ih => simpa [Finset.prod_range_succ] using ih.mul (hf N)

lemma hasCoeffs_oneSubPS (e : ℕ) : HasCoeffs (fun q => 1 - q ^ e) (oneSubPS e) := by
  intro q _
  have h : ∀ n, ((PowerSeries.coeff n (oneSubPS e) : ℤ) : ℂ) * q ^ n =
      (if n = 0 then (1 : ℂ) else 0) - (if n = e then q ^ e else 0) := by
    intro n
    simp only [oneSubPS, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    split_ifs with h1 h2 h2 <;> subst_vars <;> simp
  simp only [h]
  refine ⟨summable_of_ne_finset_zero (s := {0, e}) ?_,
    (hasSum_ite_eq 0 1).sub (hasSum_ite_eq e _)⟩
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [hn.1, hn.2]

lemma hasCoeffs_geomPS {e : ℕ} (he : 1 ≤ e) :
    HasCoeffs (fun q => (1 - q ^ e)⁻¹) (geomPS e) := by
  intro q hq
  have hqe : ‖q ^ e‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hinj : Function.Injective (fun k : ℕ => e * k) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hzero : ∀ x ∉ Set.range (fun k : ℕ => e * k),
      ((PowerSeries.coeff x (geomPS e) : ℤ) : ℂ) * q ^ x = 0 := by
    intro x hx
    have : ¬ e ∣ x := fun ⟨k, hk⟩ => hx ⟨k, hk.symm⟩
    simp [geomPS, PowerSeries.coeff_mk, this]
  have hcomp : ((fun n => ((PowerSeries.coeff n (geomPS e) : ℤ) : ℂ) * q ^ n) ∘
      fun k : ℕ => e * k) = fun k => (q ^ e) ^ k := by
    funext k
    simp [geomPS, PowerSeries.coeff_mk, pow_mul]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (fun x hx => by rw [hzero x hx, norm_zero])]
    have : ((fun n => ‖((PowerSeries.coeff n (geomPS e) : ℤ) : ℂ) * q ^ n‖) ∘
        fun k : ℕ => e * k) = fun k => ‖q ^ e‖ ^ k := by
      funext k
      have := congrFun hcomp k
      simp only [Function.comp_apply] at this ⊢
      rw [this, norm_pow]
    rw [this]
    exact summable_geometric_of_lt_one (norm_nonneg _) hqe
  · rw [← hinj.hasSum_iff hzero, hcomp]
    exact hasSum_geometric_of_norm_lt_one hqe

/-! ### Taylor coefficients and locally uniform limits -/

/-- The coefficients of an absolutely convergent power series on the unit disc are its
Taylor coefficients at `0`. -/
lemma iteratedDeriv_eq_of_hasSum {f : ℂ → ℂ} {A : ℕ → ℂ}
    (h : ∀ q : ℂ, ‖q‖ < 1 →
      Summable (fun n => ‖A n * q ^ n‖) ∧ HasSum (fun n => A n * q ^ n) (f q))
    (n : ℕ) : iteratedDeriv n f 0 = n.factorial * A n := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A
  have hr : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have := (h ((1 / 2 : NNReal) : ℂ) (by norm_num)).1
    convert this using 2 with k
    simp [p, norm_pow]
  have hp : HasFPowerSeriesOnBall f p 0 (1 / 2 : NNReal) := by
    refine ⟨hr, by norm_num, fun {y} hy => ?_⟩
    have hy' : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have : ‖y‖₊ < 1 / 2 := by exact_mod_cast hy
      have : ‖y‖ < 1 / 2 := by exact_mod_cast this
      linarith
    simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    exact (h y hy').2
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hp.factorial_smul 1 n]
  simp [p]

lemma analyticOnNhd_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (h : AnalyticOnNhd ℂ f U) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Iterated derivatives of a locally uniformly convergent family of holomorphic functions
converge locally uniformly. -/
lemma tendstoLocallyUniformlyOn_iteratedDeriv {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) φ U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    exact ih.deriv (Eventually.of_forall fun i =>
      (analyticOnNhd_iteratedDeriv ((hF i).analyticOnNhd hU) n).differentiableOn) hU

lemma tendstoLocallyUniformlyOn_pow {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f φ U) (hc : ContinuousOn f U)
    (ℓ : ℕ) : TendstoLocallyUniformlyOn (fun i q => F i q ^ ℓ) (fun q => f q ^ ℓ) φ U := by
  induction ℓ with
  | zero =>
    simp only [pow_zero]
    exact fun u hu x _ => ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  | succ ℓ ih =>
    simp only [pow_succ]
    exact ih.mul₀ hf (hc.pow ℓ) hc

/-- If holomorphic `P N → g` locally uniformly on the unit disc, `P N = ∑ A_N(n) qⁿ`, and the
coefficients `A_N(n)` are eventually `a(n)`, then `g = ∑ a(n) qⁿ` on the disc. -/
theorem hasSum_of_tendstoLocallyUniformlyOn {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {A : ℕ → PowerSeries ℤ} {a : ℕ → ℤ}
    (hP : TendstoLocallyUniformlyOn P g atTop (Metric.ball 0 1))
    (hPd : ∀ N, DifferentiableOn ℂ (P N) (Metric.ball 0 1))
    (hA : ∀ N, HasCoeffs (P N) (A N))
    (hstab : ∀ n, ∀ᶠ N in atTop, PowerSeries.coeff n (A N) = a n)
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun n => (a n : ℂ) * q ^ n) (g q) := by
  have hU : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    hP.differentiableOn (Eventually.of_forall hPd) hU
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hcoef : ∀ n, iteratedDeriv n g 0 = n.factorial * (a n : ℂ) := by
    intro n
    have ht := (tendstoLocallyUniformlyOn_iteratedDeriv hP hPd hU n).tendsto_at h0
    have hev : ∀ᶠ N in atTop, iteratedDeriv n (P N) 0 = n.factorial * (a n : ℂ) := by
      filter_upwards [hstab n] with N hN
      rw [iteratedDeriv_eq_of_hasSum (A := fun k => ((PowerSeries.coeff k (A N) : ℤ) : ℂ))
        (hA N) n, hN]
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun N h => h.symm))
  have := Complex.hasSum_taylorSeries_on_ball hg (z := q) (by simpa using hq)
  have hfun : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (q - 0) ^ n • iteratedDeriv n g 0) =
      fun n => (a n : ℂ) * q ^ n := by
    funext n
    rw [hcoef n, sub_zero, smul_eq_mul, smul_eq_mul]
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
  rwa [hfun] at this

/-! ### Infinite products on the unit disc -/

/-- A product `∏ u_j` with `‖u_j(x) - 1‖ ≤ C_r r^j` on `‖x‖ ≤ r < 1` converges locally
uniformly on the unit disc. -/
lemma hasProdLocallyUniformlyOn_ball {u : ℕ → ℂ → ℂ}
    (hcont : ∀ j, ContinuousOn (u j) (Metric.ball 0 1))
    (hbd : ∀ r : ℝ, r < 1 → ∃ C : ℝ, ∀ j x, ‖x‖ ≤ r → ‖u j x - 1‖ ≤ C * r ^ j) :
    HasProdLocallyUniformlyOn u (fun x => ∏' j, u j x) (Metric.ball 0 1) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hKc
  obtain ⟨r, hr, hKr⟩ := exists_pos_lt_subset_ball one_pos hKc.isClosed hK
  obtain ⟨C, hC⟩ := hbd r hr.2
  have h := Summable.hasProdUniformlyOn_nat_one_add (f := fun j x => u j x - 1) hKc
    ((summable_geometric_of_lt_one hr.1.le hr.2).mul_left C)
    (Eventually.of_forall fun j x hx => hC j x (by
      have := hKr hx
      rw [mem_ball_zero_iff] at this
      exact this.le))
    (fun j => ((hcont j).mono hK).sub continuousOn_const)
  simpa using h

lemma multipliable_and_tprod_ne_zero {u : ℕ → ℂ} {C r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hC : ∀ j, ‖u j - 1‖ ≤ C * r ^ j) (hne : ∀ j, u j ≠ 0) :
    Multipliable u ∧ ∏' j, u j ≠ 0 := by
  have hs : Summable fun j => ‖u j - 1‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hC
    ((summable_geometric_of_lt_one hr0 hr).mul_left C)
  have h1 := multipliable_one_add_of_summable hs
  have h2 := tprod_one_add_ne_zero_of_summable (f := fun j => u j - 1) (by simpa using hne) hs
  simp only [add_sub_cancel] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Estimates for the factors -/

lemma norm_one_sub_pow_ge {q : ℂ} {e : ℕ} (hq : ‖q‖ < 1) (he : 1 ≤ e) :
    1 - ‖q‖ ≤ ‖1 - q ^ e‖ := by
  have : ‖q ^ e‖ ≤ ‖q‖ := by
    rw [norm_pow]; exact pow_le_of_le_one (norm_nonneg _) hq.le (by omega)
  calc 1 - ‖q‖ ≤ ‖(1 : ℂ)‖ - ‖q ^ e‖ := by rw [norm_one]; linarith
    _ ≤ ‖1 - q ^ e‖ := norm_sub_norm_le _ _

lemma one_sub_pow_ne_zero {q : ℂ} {e : ℕ} (hq : ‖q‖ < 1) (he : 1 ≤ e) : 1 - q ^ e ≠ 0 := by
  intro h
  have := norm_one_sub_pow_ge hq he
  rw [h, norm_zero] at this
  linarith

lemma norm_quot_sub_one_le (a b c d : ℂ) {s ρ : ℝ} (hρ : 0 < ρ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s)
    (hc : ‖c‖ ≤ s) (hd : ‖d‖ ≤ s) (hs : s ≤ 1) (hc' : ρ ≤ ‖1 - c‖) (hd' : ρ ≤ ‖1 - d‖) :
    ‖(1 - a) * (1 - b) / ((1 - c) * (1 - d)) - 1‖ ≤ 6 * s / ρ ^ 2 := by
  have hc0 : 1 - c ≠ 0 := by intro h; rw [h, norm_zero] at hc'; linarith
  have hd0 : 1 - d ≠ 0 := by intro h; rw [h, norm_zero] at hd'; linarith
  have hs0 : 0 ≤ s := (norm_nonneg a).trans ha
  rw [div_sub_one (mul_ne_zero hc0 hd0), norm_div, norm_mul]
  have hnum : ‖(1 - a) * (1 - b) - (1 - c) * (1 - d)‖ ≤ 6 * s := by
    have e : (1 - a) * (1 - b) - (1 - c) * (1 - d) = c + d - a - b + a * b - c * d := by ring
    rw [e]
    have hab : ‖a * b‖ ≤ s := by
      rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
    have hcd : ‖c * d‖ ≤ s := by
      rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg d]
    have := norm_sub_le (c + d - a - b + a * b) (c * d)
    have := norm_add_le (c + d - a - b) (a * b)
    have := norm_sub_le (c + d - a) b
    have := norm_sub_le (c + d) a
    have := norm_add_le c d
    linarith
  rw [sq]
  gcongr

lemma exps_ge (m j : ℕ) (hm : 3 ≤ m) :
    m * j + 1 ≤ m * j + m - 1 ∧ m * j + 1 ≤ m * j + 2 ∧ m * j + 1 ≤ m * j + m - 2 := by
  omega

lemma norm_pow_le_of_ge {q : ℂ} (hq : ‖q‖ < 1) {k e : ℕ} (h : k ≤ e) : ‖q ^ e‖ ≤ ‖q‖ ^ k := by
  rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hq.le h

lemma norm_factorFan_sub_one_le {m : ℕ} (hm : 3 ≤ m) (j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    ‖factorFan m j q - 1‖ ≤ 6 * ‖q‖ ^ (m * j + 1) / (1 - ‖q‖) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := exps_ge m j hm
  exact norm_quot_sub_one_le _ _ _ _ (by linarith) (norm_pow_le_of_ge hq le_rfl)
    (norm_pow_le_of_ge hq h1) (norm_pow_le_of_ge hq h2) (norm_pow_le_of_ge hq h3)
    (pow_le_one₀ (norm_nonneg _) hq.le) (norm_one_sub_pow_ge hq (by omega))
    (norm_one_sub_pow_ge hq (by omega))

lemma inv_factorFan_eq (m j : ℕ) (q : ℂ) : (factorFan m j q)⁻¹ =
    (1 - q ^ (m * j + 2)) * (1 - q ^ (m * j + m - 2)) /
      ((1 - q ^ (m * j + 1)) * (1 - q ^ (m * j + m - 1))) := by
  rw [factorFan, inv_div]

lemma norm_inv_factorFan_sub_one_le {m : ℕ} (hm : 3 ≤ m) (j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    ‖(factorFan m j q)⁻¹ - 1‖ ≤ 6 * ‖q‖ ^ (m * j + 1) / (1 - ‖q‖) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := exps_ge m j hm
  rw [inv_factorFan_eq]
  exact norm_quot_sub_one_le _ _ _ _ (by linarith) (norm_pow_le_of_ge hq h2)
    (norm_pow_le_of_ge hq h3) (norm_pow_le_of_ge hq le_rfl) (norm_pow_le_of_ge hq h1)
    (pow_le_one₀ (norm_nonneg _) hq.le) (norm_one_sub_pow_ge hq (by omega))
    (norm_one_sub_pow_ge hq (by omega))

/-- The uniform bound `6 ‖q‖^{mj+1}/(1-‖q‖)² ≤ 6 (1-r)^{-2} r^j` on `‖q‖ ≤ r`. -/
lemma factor_bound_le {m j : ℕ} (hm : 1 ≤ m) {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    6 * ‖q‖ ^ (m * j + 1) / (1 - ‖q‖) ^ 2 ≤ 6 / (1 - r) ^ 2 * r ^ j := by
  have hq : ‖q‖ < 1 := hqr.trans_lt hr
  have hq1 : 0 < 1 - ‖q‖ := by linarith
  have hr1 : 0 < 1 - r := by linarith
  have h1 : ‖q‖ ^ (m * j + 1) ≤ r ^ j := by
    calc ‖q‖ ^ (m * j + 1) ≤ ‖q‖ ^ j :=
          pow_le_pow_of_le_one (norm_nonneg _) hq.le
            (Nat.le_succ_of_le (Nat.le_mul_of_pos_left j hm))
      _ ≤ r ^ j := pow_le_pow_left₀ (norm_nonneg _) hqr j
  have h2 : (1 - r) ^ 2 ≤ (1 - ‖q‖) ^ 2 := pow_le_pow_left₀ hr1.le (by linarith) 2
  have hrj : 0 ≤ r ^ j := pow_nonneg ((norm_nonneg _).trans hqr) j
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hq1 2) (pow_pos hr1 2)]
  nlinarith [mul_le_mul h1 h2 (pow_nonneg hr1.le 2) hrj]

lemma factorFan_ne_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    factorFan m j q ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (one_sub_pow_ne_zero hq (by omega)) (one_sub_pow_ne_zero hq (by omega)))
    (mul_ne_zero (one_sub_pow_ne_zero hq (by omega)) (one_sub_pow_ne_zero hq (by omega)))

lemma differentiableOn_factorFan {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    DifferentiableOn ℂ (factorFan m j) (Metric.ball 0 1) := by
  intro q hq
  rw [mem_ball_zero_iff] at hq
  apply DifferentiableAt.differentiableWithinAt
  unfold factorFan
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (mul_ne_zero (one_sub_pow_ne_zero hq (by omega)) (one_sub_pow_ne_zero hq (by omega)))

lemma differentiableOn_inv_factorFan {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    DifferentiableOn ℂ (fun q => (factorFan m j q)⁻¹) (Metric.ball 0 1) := by
  intro q hq
  rw [mem_ball_zero_iff] at hq
  apply DifferentiableAt.differentiableWithinAt
  simp only [inv_factorFan_eq]
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (mul_ne_zero (one_sub_pow_ne_zero hq (by omega)) (one_sub_pow_ne_zero hq (by omega)))

lemma hasCoeffs_factorF {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    HasCoeffs (factorFan m j) (factorF m j) := by
  refine ((((hasCoeffs_oneSubPS _).mul (hasCoeffs_oneSubPS _)).mul
    (hasCoeffs_geomPS (e := m * j + 2) (by omega))).mul
    (hasCoeffs_geomPS (e := m * j + m - 2) (by omega))).congr fun q _ => ?_
  rw [factorFan, div_eq_mul_inv, mul_inv]
  ring

lemma hasCoeffs_factorFt {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    HasCoeffs (fun q => (factorFan m j q)⁻¹) (factorFt m j) := by
  refine ((((hasCoeffs_oneSubPS _).mul (hasCoeffs_oneSubPS _)).mul
    (hasCoeffs_geomPS (e := m * j + 1) (by omega))).mul
    (hasCoeffs_geomPS (e := m * j + m - 1) (by omega))).congr fun q _ => ?_
  rw [inv_factorFan_eq, div_eq_mul_inv, mul_inv]
  ring

lemma hasProdLocallyUniformlyOn_Fan {m : ℕ} (hm : 3 ≤ m) :
    HasProdLocallyUniformlyOn (fun j q => factorFan m j q) (Fan m) (Metric.ball 0 1) :=
  hasProdLocallyUniformlyOn_ball (fun j => (differentiableOn_factorFan hm j).continuousOn)
    fun r hr => ⟨6 / (1 - r) ^ 2, fun j x hx =>
      (norm_factorFan_sub_one_le hm j (hx.trans_lt hr)).trans
        (factor_bound_le (by omega) hx hr)⟩

lemma hasProdLocallyUniformlyOn_Ftan {m : ℕ} (hm : 3 ≤ m) :
    HasProdLocallyUniformlyOn (fun j q => (factorFan m j q)⁻¹) (Ftan m) (Metric.ball 0 1) :=
  hasProdLocallyUniformlyOn_ball (fun j => (differentiableOn_inv_factorFan hm j).continuousOn)
    fun r hr => ⟨6 / (1 - r) ^ 2, fun j x hx =>
      (norm_inv_factorFan_sub_one_le hm j (hx.trans_lt hr)).trans
        (factor_bound_le (by omega) hx hr)⟩

lemma multipliable_factorFan {m : ℕ} (hm : 3 ≤ m) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun j => factorFan m j q) ∧ ∏' j, factorFan m j q ≠ 0 :=
  multipliable_and_tprod_ne_zero (norm_nonneg q) hq
    (fun j => (norm_factorFan_sub_one_le hm j hq).trans
      (factor_bound_le (by omega) le_rfl hq))
    (fun j => factorFan_ne_zero hm j hq)

/-- Locally uniform convergence of the `𝓁`-th powers of the partial products. -/
lemma tendsto_partial_pow {u : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (h : HasProdLocallyUniformlyOn u g (Metric.ball 0 1))
    (hd : ∀ j, DifferentiableOn ℂ (u j) (Metric.ball 0 1)) (ℓ : ℕ) :
    TendstoLocallyUniformlyOn (fun N q => (∏ j ∈ Finset.range N, u j q) ^ ℓ)
      (fun q => g q ^ ℓ) atTop (Metric.ball 0 1) := by
  have h' := h.tendstoLocallyUniformlyOn_finsetRange
  have hpd : ∀ N, DifferentiableOn ℂ (fun q => ∏ j ∈ Finset.range N, u j q) (Metric.ball 0 1) :=
    fun N => DifferentiableOn.fun_finsetProd fun j _ => hd j
  exact tendstoLocallyUniformlyOn_pow h'
    (h'.differentiableOn (Eventually.of_forall hpd) Metric.isOpen_ball).continuousOn ℓ

theorem Fan_ne_zero (m : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) : Fan m q ≠ 0 :=
  (multipliable_factorFan hm hq).2

theorem Ftan_eq_inv (m : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) : Ftan m q = (Fan m q)⁻¹ :=
  (multipliable_factorFan hm hq).1.tprod_inv₀ (multipliable_factorFan hm hq).2

/-- `∑_{n ≥ 0} c^{[𝓁]}_m(n) qⁿ = F_m(q)^𝓁` for `|q| < 1`. -/
theorem hasSum_coeffC (m ℓ : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (coeffC m ℓ n : ℂ) * q ^ n) (Fan m q ^ ℓ) :=
  hasSum_of_tendstoLocallyUniformlyOn (g := fun q => Fan m q ^ ℓ)
    (tendsto_partial_pow (hasProdLocallyUniformlyOn_Fan hm) (differentiableOn_factorFan hm) ℓ)
    (fun N => (DifferentiableOn.fun_finsetProd fun j _ =>
      differentiableOn_factorFan hm j).pow ℓ)
    (fun N => (HasCoeffs.prod_range (hasCoeffs_factorF hm) N).pow ℓ)
    (fun n => (eventually_gt_atTop n).mono fun N hN =>
      coeffC_eq_partial m ℓ n N (by omega) hN)
    hq

/-- `∑_{n ≥ 0} γ^{[λ]}_m(n) qⁿ = F̃_m(q)^λ` for `|q| < 1`. -/
theorem hasSum_coeffGamma (m lam : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (coeffGamma m lam n : ℂ) * q ^ n) (Ftan m q ^ lam) :=
  hasSum_of_tendstoLocallyUniformlyOn (g := fun q => Ftan m q ^ lam)
    (tendsto_partial_pow (hasProdLocallyUniformlyOn_Ftan hm) (differentiableOn_inv_factorFan hm)
      lam)
    (fun N => (DifferentiableOn.fun_finsetProd fun j _ =>
      differentiableOn_inv_factorFan hm j).pow lam)
    (fun N => (HasCoeffs.prod_range (hasCoeffs_factorFt hm) N).pow lam)
    (fun n => (eventually_gt_atTop n).mono fun N hN =>
      coeffGamma_eq_partial m lam n N (by omega) hN)
    hq

lemma factorFan_conj (m j : ℕ) (q : ℂ) :
    factorFan m j (starRingEnd ℂ q) = starRingEnd ℂ (factorFan m j q) := by
  simp [factorFan, map_div₀]

theorem Fan_conj (m : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) :
    Fan m (starRingEnd ℂ q) = starRingEnd ℂ (Fan m q) := by
  rw [Fan, Fan, (multipliable_factorFan hm hq).1.map_tprod (starRingEnd ℂ) continuous_conj]
  simp only [factorFan_conj]

theorem Ftan_conj (m : ℕ) (hm : 3 ≤ m) (q : ℂ) (hq : ‖q‖ < 1) :
    Ftan m (starRingEnd ℂ q) = starRingEnd ℂ (Ftan m q) := by
  have hq' : ‖starRingEnd ℂ q‖ < 1 := by simpa using hq
  rw [Ftan_eq_inv m hm _ hq', Ftan_eq_inv m hm q hq, Fan_conj m hm q hq, map_inv₀]

end ThetaSignPatterns
