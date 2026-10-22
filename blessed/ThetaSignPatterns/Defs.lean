import Mathlib

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# Definitions

Every object that appears in the statements of the paper

  K. Banerjee, K. Bringmann, B. Heim, B. Kane,
  *On sign patterns of Fourier coefficients of theta quotients*

and in the statements of the external results it relies on.
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

noncomputable section

/-! ## The Jacobi theta function -/

/-- The Jacobi theta function
`ϑ(w;τ) = ∑_{n ∈ ℤ + 1/2} q^{n²/2} e^{2πin(w+1/2)}`, `q = e^{2πiτ}`,
summed over `n = k + 1/2`, `k ∈ ℤ`. -/
def theta (w τ : ℂ) : ℂ :=
  ∑' k : ℤ, cexp (π * I * ((k : ℂ) + 1 / 2) ^ 2 * τ) *
    cexp (2 * π * I * ((k : ℂ) + 1 / 2) * (w + 1 / 2))

/-! ## Infinite products -/

/-- The analytic q-Pochhammer symbol `(a;q)_∞ = ∏_{n ≥ 0} (1 - a qⁿ)`. -/
def qPochInf (a q : ℂ) : ℂ := ∏' n : ℕ, (1 - a * q ^ n)

/-- The `j`-th factor of `F_m(q) = (q, q^{m-1}; q^m)_∞ / (q², q^{m-2}; q^m)_∞`. -/
def factorFan (m j : ℕ) (q : ℂ) : ℂ :=
  (1 - q ^ (m * j + 1)) * (1 - q ^ (m * j + m - 1)) /
    ((1 - q ^ (m * j + 2)) * (1 - q ^ (m * j + m - 2)))

/-- The theta quotient `F_m(q) = (q, q^{m-1}; q^m)_∞ / (q², q^{m-2}; q^m)_∞` of (1.2),
as a function of `q` with `|q| < 1`. -/
def Fan (m : ℕ) (q : ℂ) : ℂ := ∏' j : ℕ, factorFan m j q

/-- The inverse quotient `F̃_m(q) = (q², q^{m-2}; q^m)_∞ / (q, q^{m-1}; q^m)_∞`
of Section 1 (written `𝓕_m` in the paper). -/
def Ftan (m : ℕ) (q : ℂ) : ℂ := ∏' j : ℕ, (factorFan m j q)⁻¹

/-! ## Fourier coefficients (formal power series over `ℤ`) -/

/-- The formal geometric series `1/(1 - X^e) = ∑_{e ∣ n} Xⁿ`. -/
def geomPS (e : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => if e ∣ n then 1 else 0

/-- `1 - X^e`. -/
def oneSubPS (e : ℕ) : PowerSeries ℤ := 1 - PowerSeries.X ^ e

/-- The `j`-th factor of `F_m` as a formal power series. -/
def factorF (m j : ℕ) : PowerSeries ℤ :=
  oneSubPS (m * j + 1) * oneSubPS (m * j + m - 1) * geomPS (m * j + 2) * geomPS (m * j + m - 2)

/-- The `j`-th factor of `F̃_m` as a formal power series. -/
def factorFt (m j : ℕ) : PowerSeries ℤ :=
  oneSubPS (m * j + 2) * oneSubPS (m * j + m - 2) * geomPS (m * j + 1) * geomPS (m * j + m - 1)

/-- The coefficients `c^{[𝓁]}_m(n)` of `F_m(q)^𝓁 = ∑ c^{[𝓁]}_m(n) qⁿ` (1.2). The factors with
index `j > n` are `≡ 1 (mod X^{n+1})`, so the product over `j ≤ n` already has the right
`n`-th coefficient (`coeffC_eq_partial` in `Formal.lean`). -/
def coeffC (m ℓ n : ℕ) : ℤ :=
  PowerSeries.coeff n ((∏ j ∈ Finset.range (n + 1), factorF m j) ^ ℓ)

/-- The coefficients `γ^{[λ]}_m(n)` of `F̃_m(q)^λ = ∑ γ^{[λ]}_m(n) qⁿ`. -/
def coeffGamma (m lam n : ℕ) : ℤ :=
  PowerSeries.coeff n ((∏ j ∈ Finset.range (n + 1), factorFt m j) ^ lam)

/-! ## Modular objects -/

/-- The quotient `G_m(τ) = ϑ(τ; mτ) / ϑ(2τ; mτ)` of Section 3. -/
def Gm (m : ℕ) (τ : ℂ) : ℂ := theta τ (m * τ) / theta (2 * τ) (m * τ)

/-- The weight-`1/2` theta functions `q^{λ²/2} ϑ(λτ; τ)` of Lemma 2.2 (5). -/
def thetaRat (lam : ℚ) (τ : ℂ) : ℂ := cexp (π * I * (lam : ℂ) ^ 2 * τ) * theta (lam * τ) τ

/-- The modular function `q^{-3𝓁/(2m)} G_m(τ)^𝓁 = q^{-3𝓁/(2m) + 𝓁/2} F_m(q)^𝓁` of the proof
of Theorem 1.1, written as `((q^{1/(2m)} ϑ(τ;mτ)) / (q^{2/m} ϑ(2τ;mτ)))^𝓁`. -/
def fMod (m ℓ : ℕ) (τ : ℂ) : ℂ :=
  ((cexp (π * I * τ / m) * theta τ (m * τ)) / (cexp (4 * π * I * τ / m) * theta (2 * τ) (m * τ)))
    ^ ℓ

/-- The modular function `q^{3λ/(2m) - λ/2} F̃_m(q)^λ` of the proof of Theorem 1.5. -/
def fModT (m lam : ℕ) (τ : ℂ) : ℂ :=
  ((cexp (4 * π * I * τ / m) * theta (2 * τ) (m * τ)) / (cexp (π * I * τ / m) * theta τ (m * τ)))
    ^ lam

/-- The action of `γ ∈ SL₂(ℤ)` by Möbius transformations. -/
def mob (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)

/-- The automorphy factor `cτ + d`. -/
def jfac (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1

/-- `f` is a *weakly holomorphic modular form of weight `k` with a unitary multiplier system
on a subgroup of finite index of `SL₂(ℤ)`*:
* `f` is holomorphic on the upper half-plane;
* there are a finite-index subgroup `Γ` and a function `χ` with `|χ(γ)| = 1` and
  `f(γτ) = χ(γ) (cτ+d)^k f(τ)` for all `γ ∈ Γ` (principal branch of `(cτ+d)^k`);
* `f` is meromorphic at every cusp: for every `γ ∈ SL₂(ℤ)`,
  `(cτ+d)^{-k} f(γτ) = O(e^{A Im τ})` for `Im τ ≥ T`. -/
def IsWHModular (k : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im} ∧
  ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), Γ.FiniteIndex ∧
    ∃ χ : Matrix.SpecialLinearGroup (Fin 2) ℤ → ℂ, (∀ γ ∈ Γ, ‖χ γ‖ = 1) ∧
      (∀ γ ∈ Γ, ∀ τ : ℂ, 0 < τ.im → f (mob γ τ) = χ γ * jfac γ τ ^ (k : ℂ) * f τ) ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ A C T : ℝ, ∀ τ : ℂ, T ≤ τ.im →
        ‖jfac γ τ ^ (-(k : ℂ)) * f (mob γ τ)‖ ≤ C * Real.exp (A * τ.im)

/-- `f` is bounded below by `c e^{-A Im τ}` near every cusp (true for every nonzero
holomorphic modular form, whose expansion at each cusp has a nonzero leading term). -/
def HasCuspLowerBound (k : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ A c T : ℝ, 0 < c ∧ ∀ τ : ℂ, T ≤ τ.im →
    c * Real.exp (-(A * τ.im)) ≤ ‖jfac γ τ ^ (-(k : ℂ)) * f (mob γ τ)‖

/-- A reduced cusp `h/k` with `0 ≤ h < k` and `gcd(h,k) = 1`, as a pair `(h, k)`. -/
def IsReducedCusp (p : ℤ × ℕ) : Prop := 0 ≤ p.1 ∧ p.1 < p.2 ∧ Int.gcd p.1 p.2 = 1

/-! ## Analytic auxiliaries -/

/-- The region `R_Δ = {x + iy : x > 0, |y| ≤ Δ x}` of Section 2.3. -/
def cone (Δ : ℝ) : Set ℂ := {z : ℂ | 0 < z.re ∧ |z.im| ≤ Δ * z.re}

/-- The modified Bessel function `I₁(x) = ∑_{j ≥ 0} (x/2)^{2j+1} / (j! (j+1)!)`. -/
def besselI1 (x : ℝ) : ℝ :=
  ∑' j : ℕ, (x / 2) ^ (2 * j + 1) / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))

/-- The contribution of one dominant cusp `p = h/k` (constant `C`) to the exact formula of
Theorem 2.1 in weight `0`, after the leading principal exponent has been written through the
cusp growth constant `Λ` (see `ASSUMPTIONS.md`, refinement R1):
`√(2πΛ/(n+δ)) · C · e^{-2πi(n+δ)h/k} · I₁(√(8πΛ(n+δ)))`. -/
def rzTerm (Λ δ : ℝ) (p : ℤ × ℕ) (C : ℂ) (n : ℕ) : ℂ :=
  (Real.sqrt (2 * π * Λ / (n + δ)) : ℂ) * C *
    cexp (-(2 * π * I * ((n : ℂ) + δ) * p.1 / p.2)) *
    (besselI1 (Real.sqrt (8 * π * Λ * (n + δ))) : ℂ)

/-! ## Constants and sign data of the main results -/

/-- `φ_m = (1/2)(1 - 2/m)(1 - 3/m)` (1.3). -/
def phiM (m : ℕ) : ℝ := (1 / 2) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ))

/-- The indicator `χ_P`, as a natural number. -/
def chi (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

/-- The interval `S^{[𝓁]}_{m,1}` of Corollary 1.2 (as a predicate on integers `r`). -/
def S1 (m ℓ : ℕ) (r : ℤ) : Prop :=
  if Even ℓ then
    ((m : ℚ) + 1) / 2 - 5 * ℓ / 2 ≤ r ∧ (r : ℚ) ≤ (3 * m - 1) / 2 - 5 * ℓ / 2
  else
    (m : ℚ) - (5 * ℓ - 1) / 2 ≤ r ∧ (r : ℚ) ≤ 2 * m - (5 * ℓ + 1) / 2

instance (m ℓ : ℕ) (r : ℤ) : Decidable (S1 m ℓ r) := by unfold S1; infer_instance

/-- The sign `±1` attached to `m ≡ ±1 (mod 6)` (upper sign for `m ≡ 1`). -/
def epsM (m : ℕ) : ℝ := if m % 6 = 1 then 1 else -1

/-- `T^{[λ]}_m(n) = cos(π(λ/6 - n/3 ± ((2n-λ)/(6m) + λ/m²)))` of Theorem 1.5. -/
def Tfun (m lam n : ℕ) : ℝ :=
  Real.cos (π * ((lam : ℝ) / 6 - (n : ℝ) / 3 +
    epsM m * ((2 * (n : ℝ) - lam) / (6 * m) + (lam : ℝ) / (m : ℝ) ^ 2)))

/-- The endpoints of the interval `S^{[λ],±}_{m,2}` of Corollary 1.6, with `e = ±1` the sign
of `m ≡ ±1 (mod 6)` (upper sign for `m ≡ 1`). -/
def S2bounds (m lam : ℕ) : ℚ × ℚ :=
  let e : ℚ := if m % 6 = 1 then 1 else -1
  let M : ℚ := m
  let L : ℚ := lam
  match lam % 6 with
  | 0 => ((M + 1) / 2 + L / 6, (3 * M - 1) / 2 + L / 6)
  | 1 => (((3 - e) * M + 4) / 6 + (L - 1) / 6, ((9 - e) * M - 2) / 6 + (L - 1) / 6)
  | 2 => (((3 - 2 * e) * M + 5) / 6 + (L - 2) / 6, ((9 - 2 * e) * M - 1) / 6 + (L - 2) / 6)
  | 3 => ((L + 3) / 6, M + (L - 3) / 6)
  | 4 => (((3 + 2 * e) * M + 7) / 6 + (L - 4) / 6, ((9 + 2 * e) * M + 1) / 6 + (L - 4) / 6)
  | _ => (((3 + e) * M + 8) / 6 + (L - 5) / 6, ((9 + e) * M + 2) / 6 + (L - 5) / 6)

/-- Membership in `S^{[λ],±}_{m,2}`. -/
def S2 (m lam : ℕ) (r : ℤ) : Prop := (S2bounds m lam).1 ≤ r ∧ (r : ℚ) ≤ (S2bounds m lam).2

instance (m lam : ℕ) (r : ℤ) : Decidable (S2 m lam r) := by unfold S2; infer_instance

/-- The last factor of Corollary 1.6: `1` if `λ ≡ 0,1,2`, `-1` if `λ ≡ 4,5 (mod 6)`, and the
Jacobi symbol `(m/3)` if `λ ≡ 3 (mod 6)`. -/
def epsLam (m lam : ℕ) : ℤ :=
  if lam % 6 = 3 then jacobiSym m 3 else if lam % 6 = 4 ∨ lam % 6 = 5 then -1 else 1

/-! ## Cusp data of Sections 3 and 5 -/

/-- `𝔤(x) = {x} - {x}²`. -/
def gfr (x : ℝ) : ℝ := Int.fract x - Int.fract x ^ 2

/-- The cusp exponent `A_m(h,k) = π/(μκ) (𝔤(h/d) - 𝔤(2h/d))`, `d = gcd(m,k)`, `μ = m/d`,
`κ = k/d` (Lemma 3.1, with `{μh/m} = {h/d}`). -/
def Acusp (m : ℕ) (h : ℤ) (k : ℕ) : ℝ :=
  π / (((m / Nat.gcd m k : ℕ) : ℝ) * ((k / Nat.gcd m k : ℕ) : ℝ)) *
    (gfr ((h : ℝ) / (Nat.gcd m k : ℝ)) - gfr (2 * (h : ℝ) / (Nat.gcd m k : ℝ)))

/-- `Λ_m = π(m-1)(m-3)/(4m³)`, the dominant growth rate for odd `m`. -/
def LamOdd (m : ℕ) : ℝ := π * ((m : ℝ) - 1) * ((m : ℝ) - 3) / (4 * (m : ℝ) ^ 3)

/-- `Λ'_m = π/(4m) · max(1/4, (m-3)(m-9)/m²)`, a bound at the non-dominant cusps. -/
def LamOdd' (m : ℕ) : ℝ :=
  π / (4 * (m : ℝ)) * max (1 / 4) (((m : ℝ) - 3) * ((m : ℝ) - 9) / (m : ℝ) ^ 2)

/-- The dominant cusps `(m-1)/(2m)`, `(m+1)/(2m)` for odd `m` (Lemma 3.2). -/
def domOdd (m : ℕ) : Finset (ℤ × ℕ) := {(((m : ℤ) - 1) / 2, m), (((m : ℤ) + 1) / 2, m)}

/-- `±1` according as `m ≡ ±1 (mod 6)`, as an integer. -/
def epsZ (m : ℕ) : ℤ := if m % 6 = 1 then 1 else -1

/-- `Λ̃_m = π(m²-1)/(12m³)`, the dominant growth rate for `gcd(m,6) = 1`. -/
def LamT (m : ℕ) : ℝ := π * ((m : ℝ) ^ 2 - 1) / (12 * (m : ℝ) ^ 3)

/-- `Λ̃'_m = π/(12m) · max(1/4, (m²-25)/m²)`. -/
def LamT' (m : ℕ) : ℝ := π / (12 * (m : ℝ)) * max (1 / 4) (((m : ℝ) ^ 2 - 25) / (m : ℝ) ^ 2)

/-- The dominant cusps `(m∓1)/(6m)`, `(5m±1)/(6m)` for `m ≡ ±1 (mod 6)` (Lemma 5.2). -/
def domT (m : ℕ) : Finset (ℤ × ℕ) :=
  {(((m : ℤ) - epsZ m) / 6, m), ((5 * (m : ℤ) + epsZ m) / 6, m)}

/-- The shift `δ = 𝓁(m-3)/(2m)`: `f_{m,𝓁}(τ) = ∑ c(n) e^{2πi(n+δ)τ}`. -/
def deltaMod (m ℓ : ℕ) : ℝ := (ℓ : ℝ) * ((m : ℝ) - 3) / (2 * (m : ℝ))

/-- `C_{m,(m-1)/2} = -i e^{5πi/(2m) - 3πi/m²}` (Lemma 3.3). -/
def Codd (m : ℕ) : ℂ := -I * cexp (π * I * (5 / (2 * (m : ℂ)) - 3 / (m : ℂ) ^ 2))

/-- `C_{m,(m∓1)/6} = e^{πi/6 ∓ πi/(6m) ± πi/m²}` (Lemma 5.3). -/
def CT (m : ℕ) : ℂ := cexp (π * I * (1 / 6 - (epsM m : ℂ) / (6 * m) + (epsM m : ℂ) / (m : ℂ) ^ 2))

end

end ThetaSignPatterns
