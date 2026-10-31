# Affine Dual Jacobi–Trudi Identities — Lean 4 Formalization

Lean 4 proofs and reproducibility materials for **Affine Dual Jacobi–Trudi Identities for Classical Hall–Littlewood Polynomials via Complementary Minors**, by **Helen W. J. Zhang** and **Chengdong Zhao**. The Lean formalization was developed by **Hangzhou Logicon AI Studio**.

[中文简版](docs/README.zh-CN.md) · [Reproduction and mathematical scope](docs/REPRODUCIBILITY.md) · [Citation metadata](CITATION.cff)

This repository is being prepared for publication. Its frozen formalization release is `fidelity-20261031`, software version `0.2.0-rc3`. The existing acceptance records concern the frozen release; they do not establish that this repository's GitHub CI has passed.

## Mathematical coverage

The formalization covers all **16 numbered result environments** in the paper: Theorems A and B; Lemma 2.1; Proposition 2.2; Theorem 3.1; Lemmas 3.2 and 3.3; Propositions 4.1, 4.2 and 5.1; Lemma 5.2; Proposition 5.3; Lemma 5.4; Propositions 5.5 and 6.1; and Corollary 6.2. A seventeenth aggregate certificate covers the seven zero-parameter specializations in the final sentence of Corollary 6.2. These counts describe paper results and aggregate certificate entries, rather than individual Lean declarations.

The seven cases are `B0`, `Bminus`, `Bplus`, `C0`, `Ct`, `BC`, and `Bt`. The main identities retain `n ≥ 1`. The `Bplus` and `Bt` determinant formulas require `k ≥ 1`; their normalized width-zero values are stated separately as `1`. The other five main formulas allow `k = 0`. The `Ct` identity retains its even-sublattice restriction, and the `Bplus` and `Bt` formulas retain their factors of `1/2`.

The paper interfaces use a rational-function field over the rationals, with independent indeterminates for the parameter and variables. The square-root cases use `t = τ²`. Required regularity is proved at those interfaces. Auxiliary formulas over a general field do not justify evaluating raw quotients at arbitrary poles. The separate zero-parameter certificates assume `n, k ≥ 1`. [Further conditions and the complete correspondence table](docs/REPRODUCIBILITY.md#mathematical-scope-and-certificate-map) identify the precise specification types.

## Source and evidence

| Path | Contents |
| --- | --- |
| [`formalization/`](formalization/) | Browsable files copied byte for byte from the frozen source ZIP, with the omissions listed below. |
| [`formalization/AffineDualJT/`](formalization/AffineDualJT/) | Mathematical implementation and proofs. |
| [`formalization/FidelityLean/`](formalization/FidelityLean/) | Independent specifications, object bridges, and certificates of the specification types. |
| [`artifacts/`](artifacts/) | The unchanged frozen source ZIP and additive historical verification ZIP, with their SHA-256 files. |
| [`docs/source-view-manifest.json`](docs/source-view-manifest.json) | Binding between the source archive, browsable files, and omitted paths. |
| [`tools/verify.py`](tools/verify.py) | Repository wrapper for byte checks, extraction, and the full frozen checker. |

The browsable view omits `fidelity/runs/`, `fidelity/packets/`, `fidelity/reviews/`, and `DELIVERY_MANIFEST.sha256`. The complete frozen project, including the evidence required by the checker, is in the source ZIP. Use the wrapper below to restore it. The instructions inside `formalization/README.md` are preserved from that complete project and should be applied in the extracted working directory.

The frozen manuscript is already available as [`formalization/source.tex`](formalization/source.tex) and [`formalization/source.pdf`](formalization/source.pdf). The single-file publication edition, intended for `paper/main.tex` and `paper/paper.pdf`, will be added after a public repository URL and fixed formalization commit are available. A local paper copy during preparation is not a published repository artifact.

## Reproduce

Use a POSIX shell with Python 3.10 or later, Git, Elan, and the build tools described in the [frozen setup instructions](formalization/README.md). Dependency restoration needs network access and several gigabytes of disk space. The wrapper does **not** install dependencies.

From the repository root:

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

The extracted `lean-toolchain` selects **Lean `4.35.0-rc3`** through Elan. The locked mathlib revision is **`c55e6e786f49471c72fbddbec5415808896aec1e`**. Preserve `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; do not run `lake update` or the legacy `scripts/build_rc3.sh`.

`--check-only` checks byte consistency without compiling Lean. `--prepare-only` prepares or reuses the extracted working project. With no option, the wrapper runs its original `scripts/check_fidelity.py`. A successful full run requires exit code `0`; the new report is under `build/verification/affine_dual_jt_complete/fidelity/runs/`. A plain `lake build` does not cover the separately compiled `FidelityLean` modules. See [reproduction details](docs/REPRODUCIBILITY.md) for evidence locations and failure handling.

## What is checked

`FidelityLean/Spec.lean` imports Mathlib without importing the implementation. Its proposition definitions describe independent targets; bridge theorems connect their objects to the implementation, and certificates prove the exact target types. The full checker compiles the implementation and specification/certificate modules, exports the compiled environment, checks transitive axiom dependencies, validates bound review evidence, runs supporting exact-arithmetic and mutation checks, and rebuilds the project in two fresh directories.

The mathematical axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`. The Lean kernel checks proofs of formal statements. Matching natural-language mathematics and proof routes to those statements also relies on the separately recorded agent reviews. Hashes and checker validation do not authenticate reviewer identity or establish actual understanding. The separately hashed environment-export executable has an `unsafe main` for the environment-loading API; mathematical modules may not import it.

Historical runs `acceptance-final-20261031` and `final-delivery-zip-20261031` record passing checks on the origin host. Their fresh project reconstructions shared checked, pinned dependency caches. Any current CI result must be read from the workflow for the relevant commit; the historical records are not a substitute for it.

## Attribution

The supplied statement is reproduced verbatim:

> This Lean 4 formalization was developed by Hangzhou Logicon AI Studio, with AI assistance from OpenAI Codex (GPT-6.1 Sol), under human supervision and review.

For the mathematical paper, use the authors and title in `preferred-citation` in [`CITATION.cff`](CITATION.cff). Its top-level author identifies the accompanying software artifact. No public URL or DOI is supplied while publication is being prepared.
