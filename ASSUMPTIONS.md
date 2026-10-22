# Assumption boundary

Paper: K. Banerjee, K. Bringmann, B. Heim, B. Kane, *On sign patterns of Fourier
coefficients of theta quotients* (15 pp., manuscript `paper/Signchangemerge51.pdf`,
text extraction `paper/Signchangemerge51.txt`).

## The rule

Every mathematical result the formalization assumes is an **external, cited result**.
The external results E1–E6 below are the only ones allowed. **No result proved in
Sections 3–5 of the paper is assumed.** That covers Lemmas 3.1–3.3, 4.1, 4.2 and 5.1–5.3,
Theorems 1.1, 1.3 and 1.5, Corollaries 1.2, 1.4 and 1.6, and every step inside their
proofs. All of these are proved in Lean.

Facts that are in Mathlib are used freely and are not assumptions.

Each external result is a `Prop`-valued field of the structure
`ThetaSignPatterns.ExternalResults` (file `blessed/ThetaSignPatterns/External.lean`).
Every main theorem takes `(H : ExternalResults)` as an explicit hypothesis. No `axiom`
is declared anywhere, so `#print axioms` on every main theorem shows only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The external results, as encoded

The encoding standard is that each Lean field must be implied by the cited source
statement. Wherever possible a field is strictly *weaker* than the paper's statement:
real `z` instead of complex `z`, `∃ c ≠ 0` instead of an explicit multiplier, `~`
instead of an explicit `O`-term. A weaker field assumes less.

| id | paper | sources | Lean field | how the field relates to the paper |
|----|-------|---------|------------|-------------------------------------|
| E1 | Thm 2.1 | Rademacher–Zuckerman [14], Zuckerman [18], Bringmann–Ono [6] | `rademacherZuckerman` | the dominant-cusp form of the exact formula; see *Refinement R1* |
| E2.1 | Lemma 2.2(1) | Bringmann–Heim–Kane [4, Lemma 2.1(1)] | `thetaCuspTransform` | weakened: only real `z > 0`, and the `w`-independent factor `e^{πi(h-[-h]_k)/(4k)} e^{-3πi/4} ω_{h,k}^{-3} √(i/z)` is replaced by "some `c ≠ 0`" |
| E2.3 | Lemma 2.2(3) | Jacobi triple product [4, Lemma 2.1(3)], [19, Prop. 1.3] | `thetaTripleProduct` | verbatim; `q^{1/8} := e^{πiτ/4}` |
| E2.5 | Lemma 2.2(5) | Eichler–Zagier [9], Zwegers [19] | `thetaModular` | for `λ ∈ ℚ \ ℤ`: `q^{λ²/2} ϑ(λτ;τ)` is a weakly holomorphic weight-1/2 form with unitary multiplier on a finite-index subgroup of `SL₂(ℤ)` (an explicit, standard definition `IsWHModular`), and it is bounded below at every cusp (a nonzero modular form has a nonzero leading term at each cusp) |
| E3.1 | Lemma 2.3(1) | [4, Lemma 2.1(3)] + Lemma 2.2(3),(4) | `thetaAsymp1` | weakened: `~` along vertical lines `τ = x₀ + iy`, `y → ∞` |
| E3.2 | Lemma 2.3(2) | same | `thetaAsymp2` | same weakening |
| E3.3 | Lemma 2.3(3) | same | `thetaAsymp3` | weakened: only real `z → 0⁺` |
| E3.4 | Lemma 2.3(4) | same | `thetaAsymp4` | verbatim, as `z → 0` inside every cone `R_Δ` |
| E4 | Lemma 2.4 | classical (Watson, *Bessel functions*, §7.23) | `besselI1Asymp` | verbatim, with `I₁(x) := Σ_j (x/2)^{2j+1}/(j!(j+1)!)` |
| E5 | Prop 2.5 | Ingham [12]; Bringmann–Jennings-Shaffer–Mahlburg [5, Thm 1.1] | `ingham` | verbatim with the extra hypothesis `ν > 0` (a weakening; the paper applies it with `ν > 0`) |
| E6 | Lemma 2.6 | Dedekind eta inversion (e.g. Andrews [1]) | `etaAsymp` | verbatim, `z → 0` inside every cone `R_Δ` |

Lemma 2.2(2), the elliptic quasi-periodicity, is **not** assumed. It is proved from the
series definition of `ϑ`.

Lemma 2.2(4), modular inversion, is not used by any proof, so it is not stated.

## Refinement R1: the form in which Theorem 2.1 is used

Theorem 2.1 is an exact formula: a(n) is a conditionally convergent series over all cusps h/k.
Each term is built from the principal parts `a_{h,k}(r)` of `f` at the cusp. The paper
goes from it to the asymptotics with one sentence, "Theorem 2.1 now gives". That step
uses two things:

1. A term with principal exponent `|r+δ_{h,k}|/c_k` contributes
   `I_1((4π/k)√(|r+δ|(n+δ)/c_k))`.
2. The convergence estimates of [14], [18] and [6]: Kloosterman/Salié-type bounds for the
   inner sums over `h`. These make the total of all non-maximal terms, including the
   infinite tail over `k`, of exponentially smaller order.

Neither is proved in Sections 3–5; both are part of the cited exact-formula theory. The
field `rademacherZuckerman` states exactly this standard consequence, for an arbitrary
function `f`:

* `f` is a weight-0 weakly holomorphic modular function with unitary multiplier on a
  finite-index subgroup of `SL₂(ℤ)` (`IsWHModular 0 f`);
* `f(τ) = Σ_{n≥0} a(n) e^{2πi(n+δ)τ}`;
* there is a finite set `D` of reduced cusps `h/k` (`0 ≤ h < k`, `gcd(h,k) = 1`) with
  `f((h+iz)/k) · e^{-Λk/z} → C_{h,k}` as `z → 0⁺`;
* every other reduced cusp satisfies `f((h+iz)/k) = O(e^{Λ'k/z})` with one `Λ' < Λ`.

Under these hypotheses,

```
a(n) = Σ_{h/k ∈ D} √(2πΛ/(n+δ)) · C_{h,k} · e^{-2πi(n+δ)h/k} · I_1(√(8πΛ(n+δ)))
       + o(n^{-3/4} e^{√(8πΛn)}).
```

The displayed term is the term of Theorem 2.1 for the leading principal-part exponent at
`h/k`, rewritten through the identities `|r₀+δ_{h,k}|/c_k = Λk²/(2π)` and
`C_{h,k} = a_{h,k}(r₀) e^{2πi(r₀+δ_{h,k})[-h]_k/(kc_k)}`. Both identities hold because
`f((h+iz)/k) = f_{h,k}(([-h]_k + i/z)/k)` when `κ = 0`. The shift `δ` may be any real
number: for Theorem 1.5 the natural shift is `δ < 0`, and Theorem 2.1 covers that by
reindexing `n ↦ n + N`.

Everything the paper itself does is **proved** in Lean:

* the cusp growth at every cusp (Lemmas 3.1 and 5.1);
* the uniqueness of the dominant cusps and the uniform gap `Λ' < Λ` (Lemmas 3.2 and 5.2);
* the leading constants (Lemmas 3.3 and 5.3);
* the evaluation of the two dominant terms into the stated `cos` formula, the fact that
  the formula never vanishes, and the passage from `I₁` to elementary functions (E4);
* the sign corollaries.

## Refinement R2: level raising

The paper writes "By Lemma 2.2 (5), q^{−3𝓁/(2m)} G_m^𝓁(τ) is a modular function". Getting
this from E2.5 takes three standard facts: a quotient of two weight-1/2 forms is
weight 0, powers preserve modularity, and `τ ↦ g(mτ)` is modular whenever `g` is. All
three are **proved** in Lean (`Modularity.lean`); they are not assumed.

## Consistency checks (numerical, not proof evidence)

`numerics/` holds plain-Python checks.

* Every external transcription agrees numerically with its source formula:
  `theta_checks.py` checks E2.1, E2.3, E3.1–E3.4 and E6.
* All six main results agree with the exactly computed coefficients `c^{[𝓁]}_m(n)` and
  `γ^{[λ]}_m(n)` (`coeffs.py`). The ratio of each coefficient to its asymptotic is within
  1.5% of 1 at n = 6000, and the sign corollaries hold on whole periods near
  n = 1500–12000.

A false external field would make the main theorems vacuous, though not unsound. These
checks are there to catch transcription errors of that kind.
