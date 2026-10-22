import ThetaSignPatterns.Defs

/-!
This formalization was produced by **AxiomProver**, using AxiomCode, and verified with Axile.
The mathematical paper remains the work of its named authors; see `README.md` and `PROVENANCE.md`.
-/

/-!
# External results

The cited results the paper assumes, gathered as the `Prop`-valued fields of one structure.
No `axiom` is declared: every main theorem takes `(H : ExternalResults)` as a hypothesis, so
`#print axioms` shows only Lean's standard axioms.

Each field states, for the objects defined in `Defs.lean`, a result that the paper takes
from the literature. `ASSUMPTIONS.md` lists, for each field, the source and how the Lean
statement compares with the paper's (most fields are weaker than the paper's statement).

Numbering: E1 = Theorem 2.1, E2.k = Lemma 2.2 (k), E3.k = Lemma 2.3 (k), E4 = Lemma 2.4,
E5 = Proposition 2.5, E6 = Lemma 2.6.
-/

open Complex Filter Topology Asymptotics Real

namespace ThetaSignPatterns

/-- **E1** (Theorem 2.1; H. Rademacher and H. Zuckerman, *Ann. Math.* 39 (1938) 433–462;
H. Zuckerman, *Trans. AMS* 45 (1939) 298–321; K. Bringmann and K. Ono, *Coefficients of
harmonic Maass forms*, 2008), in the dominant-cusp form in which the paper uses it.

Let `f` be a weight-`0` weakly holomorphic modular function with unitary multiplier on a
finite-index subgroup of `SL₂(ℤ)`, with `f(τ) = ∑_{n ≥ 0} a(n) e^{2πi(n+δ)τ}`. Suppose that
at the reduced cusps `h/k ∈ D` one has `f((h+iz)/k) e^{-Λk/z} → C_{h,k}` (`z → 0⁺`), and
that at every other reduced cusp `f((h+iz)/k) = O(e^{Λ'k/z})` with `Λ' < Λ`. Then the
dominant terms of the exact formula of Theorem 2.1 give `a(n)` up to
`o(n^{-3/4} e^{√(8πΛn)})`. -/
def RademacherZuckermanDominant : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℕ → ℂ) (δ Λ Λ' : ℝ) (D : Finset (ℤ × ℕ)) (C : ℤ × ℕ → ℂ),
    IsWHModular 0 f →
    (∀ τ : ℂ, 0 < τ.im → HasSum (fun n : ℕ => a n * cexp (2 * π * I * ((n : ℂ) + δ) * τ)) (f τ)) →
    0 < Λ → Λ' < Λ →
    (∀ p ∈ D, IsReducedCusp p) →
    (∀ p ∈ D, Tendsto (fun z : ℝ => f ((p.1 + I * z) / p.2) * cexp (-((Λ * p.2 / z : ℝ) : ℂ)))
      (𝓝[>] 0) (𝓝 (C p))) →
    (∀ p : ℤ × ℕ, IsReducedCusp p → p ∉ D → ∃ K : ℝ, ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ),
      ‖f ((p.1 + I * (z : ℂ)) / p.2)‖ ≤ K * Real.exp (Λ' * p.2 / z)) →
    (fun n : ℕ => a n - ∑ p ∈ D, rzTerm Λ δ p (C p) n) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (Real.sqrt (8 * π * Λ * n)))

/-- **E2.1** (Lemma 2.2 (1); K. Bringmann, B. Heim, B. Kane, *J. Math. Anal. Appl.* 548
(2025) 129339, Lemma 2.1 (1)): the transformation of `ϑ` at the cusp `h/k`. For
`hh' ≡ -1 (mod k)` and `z > 0`, `ϑ(w; (h+iz)/k) = c · e^{-πkw²/z} ϑ(iw/z; (h'+i/z)/k)` with a
nonzero factor `c` independent of `w` (in the paper,
`c = e^{πi(h-[-h]_k)/(4k)} e^{-3πi/4} ω_{h,k}^{-3} √(i/z)`). -/
def ThetaCuspTransform : Prop :=
  ∀ (h : ℤ) (k : ℕ) (h' : ℤ), 0 < k → Int.gcd h k = 1 → (k : ℤ) ∣ h * h' + 1 →
    ∀ z : ℝ, 0 < z → ∃ c : ℂ, c ≠ 0 ∧ ∀ w : ℂ,
      theta w ((h + I * z) / k) = c * cexp (-(π * k * w ^ 2 / z)) * theta (I * w / z) ((h' + I / z) / k)

/-- **E2.3** (Lemma 2.2 (3); the Jacobi triple product, [4, Lemma 2.1 (3)], S. Zwegers,
*Mock theta functions*, Prop. 1.3): for `Im τ > 0`,
`ϑ(w;τ) = -i q^{1/8} e^{-πiw} ∏_{n ≥ 1} (1-qⁿ)(1-ζq^{n-1})(1-ζ⁻¹qⁿ)`,
`q = e^{2πiτ}`, `ζ = e^{2πiw}`, `q^{1/8} = e^{πiτ/4}`. -/
def ThetaTripleProduct : Prop :=
  ∀ w τ : ℂ, 0 < τ.im →
    theta w τ = -I * cexp (π * I * τ / 4) * cexp (-(π * I * w)) *
      ∏' n : ℕ, ((1 - cexp (2 * π * I * τ) ^ (n + 1)) *
        (1 - cexp (2 * π * I * w) * cexp (2 * π * I * τ) ^ n) *
        (1 - (cexp (2 * π * I * w))⁻¹ * cexp (2 * π * I * τ) ^ (n + 1)))

/-- **E2.5** (Lemma 2.2 (5); M. Eichler and D. Zagier, *The theory of Jacobi forms*;
Zwegers, *op. cit.*): for `λ ∈ ℚ \ ℤ`, `q^{λ²/2} ϑ(λτ;τ)` is a (weakly) holomorphic modular
form of weight `1/2` with unitary multiplier on a finite-index subgroup of `SL₂(ℤ)`; being a
nonzero modular form, its expansion at each cusp has a nonzero leading term, so it is
bounded below by `c e^{-A Im τ}` near every cusp. -/
def ThetaModular : Prop :=
  ∀ lam : ℚ, (∀ n : ℤ, lam ≠ n) →
    IsWHModular (1 / 2) (thetaRat lam) ∧ HasCuspLowerBound (1 / 2) (thetaRat lam)

/-- **E3.1** (Lemma 2.3 (1); [4, Lemma 2.1 (3)]): for `0 < a < 1`, `b ∈ ℝ`, as `τ → i∞`
(here along every vertical line `τ = x₀ + iy`, `y → ∞`),
`ϑ(aτ+b;τ) ∼ -i e^{-πib} q^{1/8 - a/2}`. -/
def ThetaAsymp1 : Prop :=
  ∀ a b x₀ : ℝ, 0 < a → a < 1 →
    (fun y : ℝ => theta (a * (x₀ + I * y) + b) (x₀ + I * y)) ~[atTop]
      (fun y : ℝ => -I * cexp (-(π * I * b)) * cexp (2 * π * I * (x₀ + I * y) * (1 / 8 - a / 2)))

/-- **E3.2** (Lemma 2.3 (2)): for `b ∉ ℤ`, as `τ → i∞` (along vertical lines),
`ϑ(b;τ) ∼ -2 sin(πb) e^{πiτ/4}`. -/
def ThetaAsymp2 : Prop :=
  ∀ b x₀ : ℝ, (∀ n : ℤ, b ≠ n) →
    (fun y : ℝ => theta b (x₀ + I * y)) ~[atTop]
      (fun y : ℝ => -2 * Real.sin (π * b) * cexp (π * I * (x₀ + I * y) / 4))

/-- **E3.3** (Lemma 2.3 (3)): for `0 < b < 1` and `a ∈ ℝ`, as `z → 0⁺`,
`ϑ(aiz + b; iz) ∼ -e^{-2πiab + πia} e^{(-b² - 1/4 + b)π/z} / √z`. -/
def ThetaAsymp3 : Prop :=
  ∀ a b : ℝ, 0 < b → b < 1 →
    (fun z : ℝ => theta (a * I * z + b) (I * z)) ~[𝓝[>] 0]
      (fun z : ℝ => -cexp (-(2 * π * I * a * b) + π * I * a) *
        cexp (((-b ^ 2 - 1 / 4 + b) * π / z : ℝ)) / (Real.sqrt z : ℂ))

/-- **E3.4** (Lemma 2.3 (4)): for `a ∉ ℤ`, as `z → 0` in every cone `R_Δ`,
`ϑ(aiz; iz) ∼ -2i sin(πa) e^{-π/(4z)} / √z` (principal branch). -/
def ThetaAsymp4 : Prop :=
  ∀ a : ℝ, (∀ n : ℤ, a ≠ n) → ∀ Δ : ℝ, 0 ≤ Δ →
    (fun z : ℂ => theta (a * I * z) (I * z)) ~[𝓝[cone Δ] 0]
      (fun z : ℂ => -2 * I * Real.sin (π * a) * cexp (-(π / (4 * z))) / z ^ (1 / 2 : ℂ))

/-- **E4** (Lemma 2.4; classical, e.g. G. N. Watson, *A treatise on the theory of Bessel
functions*, §7.23): `I₁(x) ∼ eˣ/√(2πx)` as `x → ∞`. -/
def BesselI1Asymp : Prop :=
  (fun x : ℝ => besselI1 x) ~[atTop] (fun x : ℝ => Real.exp x / Real.sqrt (2 * π * x))

/-- **E5** (Proposition 2.5; A. Ingham, *Ann. Math.* 42 (1941); K. Bringmann,
C. Jennings-Shaffer, K. Mahlburg, *Ramanujan J.* 61 (2021), Theorem 1.1): Ingham's Tauberian
theorem in the form of [5]. (The hypothesis `ν > 0` is added; the paper uses `ν > 0`.) -/
def Ingham : Prop :=
  ∀ (b : ℕ → ℝ) (ν β γ : ℝ), 0 < ν → 0 < γ → (∀ n, 0 ≤ b n) → Monotone b →
    (∀ q : ℂ, ‖q‖ < 1 → Summable (fun n : ℕ => (b n : ℂ) * q ^ n)) →
    ((fun t : ℝ => ∑' n : ℕ, b n * Real.exp (-(t * n))) ~[𝓝[>] 0]
      (fun t : ℝ => ν * t ^ β * Real.exp (γ / t))) →
    (∀ Δ : ℝ, 0 ≤ Δ → (fun z : ℂ => ∑' n : ℕ, (b n : ℂ) * cexp (-(z * n))) =O[𝓝[cone Δ] 0]
      (fun z : ℂ => ‖z‖ ^ β * Real.exp (γ / ‖z‖))) →
    (fun n : ℕ => b n) ~[atTop]
      (fun n : ℕ => ν * γ ^ (β / 2 + 1 / 4) / (2 * Real.sqrt π * (n : ℝ) ^ (β / 2 + 3 / 4)) *
        Real.exp (2 * Real.sqrt (γ * n)))

/-- **E6** (Lemma 2.6; the modular inversion of Dedekind's `η`, e.g. G. Andrews, *The theory
of partitions*): with `q = e^{-z}`, `(q;q)_∞ ∼ √(2π/z) e^{-π²/(6z)}` as `z → 0` in every cone. -/
def EtaAsymp : Prop :=
  ∀ Δ : ℝ, 0 ≤ Δ →
    (fun z : ℂ => qPochInf (cexp (-z)) (cexp (-z))) ~[𝓝[cone Δ] 0]
      (fun z : ℂ => (2 * π / z) ^ (1 / 2 : ℂ) * cexp (-(π ^ 2 / (6 * z))))

/-- The external results E1–E6 used by the paper. -/
structure ExternalResults : Prop where
  rademacherZuckerman : RademacherZuckermanDominant
  thetaCuspTransform : ThetaCuspTransform
  thetaTripleProduct : ThetaTripleProduct
  thetaModular : ThetaModular
  thetaAsymp1 : ThetaAsymp1
  thetaAsymp2 : ThetaAsymp2
  thetaAsymp3 : ThetaAsymp3
  thetaAsymp4 : ThetaAsymp4
  besselI1Asymp : BesselI1Asymp
  ingham : Ingham
  etaAsymp : EtaAsymp

end ThetaSignPatterns
