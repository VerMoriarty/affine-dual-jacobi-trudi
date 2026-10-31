# fidelity-20261031 — formalization 0.2.0-rc3

This release publishes the frozen Lean 4 formalization and reproducibility materials for *Affine Dual Jacobi–Trudi Identities for Classical Hall–Littlewood Polynomials via Complementary Minors*, by Helen W. J. Zhang and Chengdong Zhao.

The stable formalization and verification-wrapper baseline is commit [`7d58ee5913d67d8036991a5a363260f24f0625bf`](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/tree/7d58ee5913d67d8036991a5a363260f24f0625bf). The release tag also includes the single-file publication edition, `paper/main.tex` and `paper/paper.pdf`, which accompanies this same formalization and retains the manuscript's author and AI-use declarations. Preparing the publication edition does not change the frozen Lean sources or constitute another Lean verification.

## Environment and mathematical scope

- Software: `0.2.0-rc3`; frozen release: `fidelity-20261031`.
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`, fixed by `lake-manifest.json`.
- Coverage: all 16 numbered theorem, proposition, lemma, and corollary environments in the paper, plus one aggregate certificate for the seven zero-parameter specializations in the final sentence of Corollary 6.2. These are paper-result and certificate-entry counts, not counts of individual Lean declarations.

The seven cases are `B0`, `Bminus`, `Bplus`, `C0`, `Ct`, `BC`, and `Bt`. Main identities assume `n ≥ 1`. The `Bplus` and `Bt` determinant formulas require `k ≥ 1`, retain their factors of `1/2`, and have separately proved normalized width-zero values of `1`; the other five main formulas allow `k = 0`. The `Ct` formula retains its even-sublattice restriction. The separate zero-parameter certificates assume `n, k ≥ 1`.

Paper interfaces use a rational-function field over the rationals with independent indeterminates; square-root cases use `t = τ²`. Required regularity is proved at these interfaces. General-field quotient formulas do not authorize arbitrary evaluation at poles. See the [complete scope and certificate map](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/blob/7d58ee5913d67d8036991a5a363260f24f0625bf/docs/REPRODUCIBILITY.md#mathematical-scope-and-certificate-map).

## Verification evidence

The frozen source and additive verification archives preserve the passing historical runs `acceptance-final-20261031` and `final-delivery-zip-20261031`. The additional local run `github-preparation-20261101` completed with `overall: pass`, no unresolved entries, and passing `kernel`, `object_correspondence`, `reproduction`, `route_correspondence`, and `statement_correspondence` dimensions. Its full compressed report is attached. This was a local macOS run reusing checked, pinned dependency caches; it is not a Linux or GitHub Actions CI result. Consult the workflow for the relevant commit for any CI outcome.

The complete checker compiles the implementation and independent specification/certificate modules, checks compiled declarations and their transitive axiom dependencies, validates bound review evidence, runs supporting exact-arithmetic and mutation checks, and performs two fresh project reconstructions. The mathematical axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

Lean's kernel verifies the formal statements. The correspondence of natural-language mathematics and proof routes to those statements also depends on the separately recorded agent reviews. The release does not automatically certify every natural-language claim; hashes and review validation do not authenticate reviewer identity or actual understanding.

## Assets and SHA-256

The frozen source ZIP contains the complete runnable project and selected fidelity evidence. The verification ZIP adds historical logs and the final extraction receipt under the same `affine_dual_jt_complete/` root; it supplements the source ZIP.

| Asset | SHA-256 |
| --- | --- |
| `affine-dual-jt-fidelity-20261031.zip` | `0a40289c30aa7fbabf19b8c08b567948f1c94ee93982acea939892912d5823dd` |
| `affine-dual-jt-fidelity-verification-20261031.zip` | `06e62ccd4320c5be9e130c81d250ac33dbac261391678a04a2eaf62522be5216` |
| `github-preparation-20261101-report.json.gz` | `8dfa17bd5d35f81c29c2c67d829c148ed38c81abe3a09f82d3b595f04323aa1f` |

Each of these three files has a companion `.sha256` asset. The release also supplies `main.tex`, `paper.pdf`, and `publication-SHA256SUMS.txt`, which records the checksums of the publication files and distributed evidence assets.

## Reproduce

Use Python 3.10 or later, Git, Elan, a POSIX build environment, network access to restore pinned dependencies, and several gigabytes of free space. From a checkout of this release:

```sh
python3 tools/verify.py --check-only
python3 tools/verify.py --prepare-only
cd build/verification/affine_dual_jt_complete
lean --version
lake --version
lake exe cache get
cd ../../..
python3 tools/verify.py
```

The wrapper does not install dependencies. Preserve `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; do not run `lake update` or the legacy `scripts/build_rc3.sh`. Byte checking and preparation alone do not establish proof acceptance, and `lake build` alone omits the separately compiled `FidelityLean` modules. A full checker exit code of `0` is required. New reports appear under `build/verification/affine_dual_jt_complete/fidelity/runs/`. See the [reproduction instructions](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/blob/7d58ee5913d67d8036991a5a363260f24f0625bf/docs/REPRODUCIBILITY.md).

## Attribution

The supplied formalization statement is retained verbatim:

> This Lean 4 formalization was developed by Hangzhou Logicon AI Studio, with AI assistance from OpenAI Codex (GPT-6.1 Sol), under human supervision and review.

For the mathematical paper, use the authors and title in `preferred-citation` in `CITATION.cff`; its top-level author identifies the accompanying software artifact.
