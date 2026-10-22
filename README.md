# ThetaSignPatterns

> **Formalization provenance:** Produced by **AxiomProver** using **AxiomCode** and verified with **Axile**.  The original mathematics and paper are credited to Banerjee, Bringmann, Heim, and Kane.


A Lean 4 / Mathlib formalization of

> K. Banerjee, K. Bringmann, B. Heim, B. Kane,
> *On sign patterns of Fourier coefficients of theta quotients* (manuscript, 15 pp.).

All six main results are formalized. Each is proved from cited external results only.

* **Theorem 1.1**, for odd `m > 3`: the asymptotic of `c^{[𝓁]}_m(n)`, with its
  constant `((1-1/m)(1-3/m)𝓁/(2m))^{1/4}`, the factor `(-1)ⁿ cos(π(φ_m 𝓁 - n/m))`, and
  the exponential `e^{π√(2(1-1/m)(1-3/m)𝓁n/m)}/n^{3/4}`; also its eventual sign.
* **Corollary 1.2**: the explicit periodic sign `(-1)^{r+⌊𝓁/2⌋+χ_{r∈S^{[𝓁]}_{m,1}}}` for `m > 6𝓁`.
* **Theorem 1.3**, for even `m ≥ 4`: the asymptotic
  `𝓁^{1/4}/(2^{𝓁+5/4} m^{1/4} sin^𝓁(2π/m)) · (-1)ⁿ e^{π√(2𝓁n/m)}/n^{3/4}`.
* **Corollary 1.4**: `sgn c^{[𝓁]}_m(n) = (-1)ⁿ` for **all** `n`.
* **Theorem 1.5**, for `gcd(m,6) = 1`: the asymptotic of `γ^{[λ]}_m(n)` with the factor
  `T^{[λ]}_m(n)`; also its eventual sign.
* **Corollary 1.6**: the explicit periodic sign for `λ < m/2`, including the Jacobi
  symbol `(m/3)`.

"Asymptotic" is Mathlib's `Asymptotics.IsEquivalent` (`u ~[atTop] v`, meaning
`u - v = o(v)`). "For `n ≫ 1`" is `∀ᶠ n in atTop`. The sign is `Real.sign`.

## Layout

| path | contents |
|---|---|
| `paper/` | the paper (PDF) and its text extraction |
| `ASSUMPTIONS.md`, `assumptions.json` | the assumption boundary: external results E1–E6, sources, how each is encoded |
| `blueprint/blueprint.tex`, `blueprint.json` | 68-node dependency blueprint, every node `\leanok` and mapped to its Lean declarations |
| `blueprint/verify_graph.py`, `bptools.py`, `mark.py` | graph verifier, JSON export and leanok marking |
| `blessed/` | the Lean project (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) |
| `blessed/ThetaSignPatterns/` | the Lean sources (below) |
| `numerics/` | plain-Python consistency checks (not proof evidence) |

Lean files, in dependency order:

* `Defs.lean`: all objects (`theta`, products, coefficients, `IsWHModular`, constants, sign data)
* `External.lean`: the external results E1–E6, as fields of the hypothesis structure `ExternalResults`
* `ThetaBasic.lean`: quasi-periodicity of `ϑ` (Lemma 2.2(2), proved)
* `Formal.lean`: formal coefficients
* `Expansion.lean`: products = power series
* `ThetaProduct.lean`: theta quotients as products
* `Modularity.lean`: quotients and level raising of modular forms (proved)
* `CuspGrowth.lean`: Lemmas 3.1 and 5.1
* `DominantCusps.lean`: Lemmas 3.2 and 5.2
* `LocalConstants.lean`: Lemmas 3.3 and 5.3
* `MainTerm.lean`: from the exact formula to closed asymptotics
* `Lemma41.lean`: Lemma 4.1
* `Theorem11.lean`, `Theorem13.lean`, `Theorem15.lean`: Sections 3, 4 and 5
* `Main.lean`: the six main results, stated in full
* `Solution.lean`: one theorem `ThetaSignPatterns.solution` bundling all of them

## Assumptions

No `axiom`, `sorry`, `native_decide` or `unsafe` appears anywhere. The cited results E1–E6
(the Rademacher–Zuckerman exact formula, theta transformation, triple product and
modularity identities, theta asymptotics, `I₁` asymptotics, Ingham's Tauberian theorem,
and the `η` asymptotic) are explicit hypotheses `H : ExternalResults`. No result proved in
Sections 3–5 of the paper is assumed. Corollary 1.4 needs no external input at all.
`ASSUMPTIONS.md` documents each external field. In particular it covers refinement R1,
the dominant-cusp form in which Theorem 2.1 is used.

## Toolchain

Lean `v4.33.1` and Mathlib `v4.33.1` (commit `0df444a360eaa60ab8c11dca51a86af692955474`), as
pinned in `blessed/lean-toolchain` and `blessed/lake-manifest.json`. The project is
checked through the Axile Lean service (scratch "blessed" layout with its own lakefile).
Locally, run `lake exe cache get && lake build` in `blessed/`.

## License

Apache-2.0 (see `LICENSE`). Cite with `CITATION.cff`.
