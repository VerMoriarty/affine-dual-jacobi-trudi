# Reproducing the frozen formalization

This [repository](https://github.com/VerMoriarty/affine-dual-jacobi-trudi) provides the [paper PDF](../paper/paper.pdf), its [single-file LaTeX source](../paper/main.tex), and release `fidelity-20261031` of the Lean software `0.2.0-rc3`. The paper references [fixed formalization commit `7d58ee5913d67d8036991a5a363260f24f0625bf`](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/tree/7d58ee5913d67d8036991a5a363260f24f0625bf). The browsable source view and repository wrapper are packaging conveniences around the unchanged frozen archives. The procedure below runs the original checker in a complete extracted project.

## Frozen bytes and browsable files

| Archive under `artifacts/` | Bytes | SHA-256 |
| --- | ---: | --- |
| `affine-dual-jt-fidelity-20261031.zip` | 19,053,813 | `0a40289c30aa7fbabf19b8c08b567948f1c94ee93982acea939892912d5823dd` |
| `affine-dual-jt-fidelity-verification-20261031.zip` | 3,643,112 | `06e62ccd4320c5be9e130c81d250ac33dbac261391678a04a2eaf62522be5216` |

Both archives use the top-level directory `affine_dual_jt_complete/`. The source ZIP contains the runnable pinned project and selected fidelity evidence. The verification ZIP adds the final source-ZIP extraction receipt and historical logs to that same project root. It does not replace the source ZIP.

The files in [`../formalization/`](../formalization/) are copied byte for byte from the source ZIP, preserving its internal relative paths. The view omits `fidelity/runs/`, `fidelity/packets/`, `fidelity/reviews/`, and `DELIVERY_MANIFEST.sha256`; these remain in the archive. [`source-view-manifest.json`](source-view-manifest.json) binds the view to the source archive and lists the omissions. In particular, omitted historical environments are referenced by the review records and must be restored before the complete checker can pass. The original full delivery manifest applies to the extracted project.

The historical frozen manuscript source is [`formalization/source.tex`](../formalization/source.tex), with its originally packaged PDF at [`formalization/source.pdf`](../formalization/source.pdf); the authoritative mathematical input in the complete extracted project is `fidelity/inputs/authoritative.pdf`, whose SHA-256 is `b13eaa9ed2a2dc2919980a702965a2d138ee634b49d9a32125ddeaa67fece7ab`. The manuscript source SHA-256 is `4141e8fa7c8fc8d7499b1d10bb77fcc1440d229169f44610709ebaf8968a5a19`. The authoritative input PDF and the originally packaged PDF have the same mathematical body but differ in their final AI-use declarations, as recorded in `fidelity/inputs/pdf_difference.txt`. Both frozen inputs are retained.

The current paper is [`paper/paper.pdf`](../paper/paper.pdf), built from [`paper/main.tex`](../paper/main.tex). The frozen manuscript files remain historical inputs; publication-file preparation does not itself constitute a new Lean verification.

## Prepare the environment and run

Use Python 3.10 or later, Git, Elan, and a POSIX build environment. The [frozen README](../formalization/README.md) describes platform prerequisites. Network access is needed to restore the Lean toolchain, dependency checkouts, and mathlib cache. Allow several gigabytes of disk space for dependencies, compilation, and fresh project reconstructions.

From the repository root, first check the distributed bytes and prepare the complete project:

```sh
python3 tools/verify.py --check-only
python3 tools/verify.py --prepare-only
```

The wrapper does not install tools or fetch dependencies. Preparation extracts or reuses `build/verification/affine_dual_jt_complete/`. Enter that directory to select the frozen toolchain and restore dependencies:

```sh
cd build/verification/affine_dual_jt_complete
lean --version
lake --version
lake exe cache get
cd ../../..
```

With Elan installed, the project's `lean-toolchain` selects `leanprover/lean4:v4.35.0-rc3`. If that toolchain needs explicit installation, run `elan toolchain install leanprover/lean4:v4.35.0-rc3` before the version checks. The expected Lean version is `4.35.0-rc3`; mathlib is locked to `c55e6e786f49471c72fbddbec5415808896aec1e`. Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` unchanged. Do not run `lake update` or the legacy `scripts/build_rc3.sh`, which can rewrite pinned configuration.

Then run the complete checker from the repository root:

```sh
python3 tools/verify.py
```

| Wrapper invocation | Scope |
| --- | --- |
| `--check-only` | Checks distributed byte consistency; does not compile Lean or establish proof acceptance. |
| `--prepare-only` | Prepares or reuses the complete extracted working directory; does not establish proof acceptance. |
| No option | Runs the original complete fidelity checker in that working directory. |

The original entrypoint, when working directly in the extracted project, is `python3 scripts/check_fidelity.py`. Each run creates a new `fidelity/runs/<run-id>/` directory. Its `report.json`, command logs, exit codes, environment exports, and hashes record that run's outcome. In the repository layout these are under `build/verification/affine_dual_jt_complete/fidelity/runs/`.

A full checker exit code of `0` is required for overall acceptance. `--static-only` and `--skip-build` are original-checker diagnostic modes and cannot establish full acceptance. The original checker has a default per-command timeout of 3600 seconds; its `--command-timeout SECONDS` option can change that limit when invoking it directly. Missing tools, timeouts, stale inputs, and unresolved evidence produce a nonzero result. Inspect the new report and referenced logs for the actual cause.

## What the complete checker does

The checker binds the mathematical inputs and checker tools to their hashes, verifies the actual compiler and dependency revisions, compiles the implementation modules, and compiles every `FidelityLean` module in import order. This last step is necessary: the frozen `lakefile.toml` declares only the `AffineDualJT` library, so `lake build` alone is not the complete verification command.

It then exports the compiled environment, checks mathematical declarations and their transitive axiom dependencies, validates independent specification certificates and recorded review evidence, checks route dependencies, and runs supporting exact-arithmetic experiments and compiled semantic mutations. It also rebuilds the project twice in fresh directories, once from a source copy and once from a newly generated ZIP. Those reconstructions start without project build artifacts and share only the checked, pinned dependency checkouts and caches.

The existing archive manifests and past reports establish received byte identity and historical outcomes. A fresh run provides current compilation evidence. Existing success labels are not used in place of new build results. The complete local `github-preparation-20261101` run is recorded below. The repository CI is intended to provide the fixed environment and invoke the same full wrapper; consult its actual result for the relevant commit. The local result is not a GitHub Actions result, and no successful GitHub CI run is claimed by this document.

## Mathematical scope and certificate map

The implementation is under `AffineDualJT/`. `FidelityLean/Spec.lean` imports Mathlib without importing implementation modules, and defines the paper's mathematical objects and proposition types in `Fidelity.Spec`. A `def ... : Prop` supplies a target, not a proof or axiom. `ZeroParameterSpec.lean` adds the separate zero-parameter targets. Coefficient and Weyl bridges prove the agreement of independently defined objects, parameters, and indices before implementation results are used to prove those targets.

The paper's symbolic field is `FractionRing (MvPolynomial (Fin (n + 1)) ℚ)`. Slot zero represents `t`, or `τ` in the square-root cases; the remaining slots represent the independent variables. Theorems establish their required nonzero properties. Lean's zero-based finite indices are translated to the paper's indices with `paperIndex i = i.val + 1`; coefficient and shift indices are integers.

All specification names below have prefix `Fidelity.Spec.`; all certificate names have prefix `Fidelity.Certificate.`. [`FidelityLean/Certificates.lean`](../formalization/FidelityLean/Certificates.lean) exposes the aggregate entrypoints.

| Paper result | Specification | Certificate |
| --- | --- | --- |
| Theorem A | `StatementTheoremA` | `accepted_A` |
| Theorem B | `StatementTheoremB` | `accepted_B` |
| Lemma 2.1 | `StatementLemma21` | `accepted_L21` |
| Proposition 2.2 | `StatementProposition22` | `accepted_P22` |
| Theorem 3.1 | `StatementTheorem31` | `accepted_T31` |
| Lemma 3.2 | `StatementLemma32` | `accepted_L32` |
| Lemma 3.3 | `StatementLemma33` | `accepted_L33` |
| Proposition 4.1 | `StatementProposition41` | `accepted_P41` |
| Proposition 4.2 | `StatementProposition42` | `accepted_P42` |
| Proposition 5.1 | `StatementProposition51` | `accepted_P51` |
| Lemma 5.2 | `StatementLemma52` | `accepted_L52` |
| Proposition 5.3 | `StatementProposition53` | `accepted_P53` |
| Lemma 5.4 | `StatementLemma54` | `accepted_L54` |
| Proposition 5.5 | `StatementProposition55` | `accepted_P55` |
| Proposition 6.1 | `StatementProposition61` | `accepted_P61` |
| Corollary 6.2 | `StatementCorollary62` | `accepted_C62` |
| Corollary 6.2, seven zero-parameter cases | `Corollary62ZeroSpecializations` | `accepted_C62_zero` |

The first 16 rows correspond to the paper's 16 numbered result environments; the final row is a separate aggregate supplement. The seven main formula certificates are `A13` (`B0`), `A14` (`Bminus`), `A15` (`Bplus`), `A16` (`C0`), `A17` (`Ct`), `A18` (`BC`), and `B19` (`Bt`). The machine-readable aggregate map is `fidelity/certificates.json`.

The main identities assume `n ≥ 1`. The `Bplus` and `Bt` determinant formulas retain `k ≥ 1` and their factors of `1/2`; their normalized `k = 0` values are separately `1`. The other five main formulas allow `k = 0`. The `Ct` formula retains the even-sublattice sum. Proposition 6.1 gives all seven normalized width-zero values. Positive-width kernel/minor applications retain their stated conditions. Lemma 3.3 quantifies over arbitrary integer-indexed sequences in the paper's field. Lemmas 5.2 and 5.4 retain positive width and nonzero parameter hypotheses.

Theorem 3.1 has an arbitrary-field interface with its kernel and nonzero-minor assumptions. The Hall–Littlewood paper interfaces prove their regularity conditions in the symbolic field. Lean's totalized division does not make auxiliary raw quotient formulas valid at every numerical pole; cancellation or polynomial continuation must be justified separately.

Corollary 6.2 and its zero-parameter supplement assume `n, k ≥ 1`. In the `Ct` case the exponent `k*y² - j*y` is zero at `j = k, y = 1`; the proof retains that term. It does not assert that every nonzero affine shift vanishes at zero parameter. The zero-parameter supplement also keeps the finite left-hand ratios separate from the half factors on the right.

## Trust and verification evidence

The mathematical transitive axiom allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`. The audit checks compiled mathematical declarations and their dependencies; source scans provide additional checks. `FidelityLean/Export.lean` has an `unsafe main` for Lean's environment-loading API. That executable is separately hashed, excluded from the mathematical import set, and forbidden as an import of mathematical modules.

Kernel verification establishes proofs of formal types. Interpretation of the paper and agreement with its proof route are supported by separately recorded isolated-agent reviews. The checker validates their structures, source bindings, packet boundaries, and dependency evidence. It does not authenticate reviewer identity, actual understanding, or attestations about fresh context. Exact-arithmetic experiments and error probes support the audit without proving the general identities.

The complete local run `github-preparation-20261101` records overall `pass`, with kernel, object correspondence, reproduction, route correspondence, and statement correspondence all `pass`. The [provenance summary](provenance/GITHUB_PREPARATION.json) records its input and tool bindings and identifies the [compressed full report](../artifacts/github-preparation-20261101-report.json.gz). The compressed report SHA-256 is `8dfa17bd5d35f81c29c2c67d829c148ed38c81abe3a09f82d3b595f04323aa1f`; the uncompressed report SHA-256 is `9e3fbb60291bb92fff25a227304ab7ffce9afd1a7a54c1dfb32df3f0e4008b2f`. The run finished at `2026-10-31T17:22:25.081+00:00` (2026-11-01 in China). It ran locally on macOS and reused the checked, pinned dependency cache. It is not a GitHub Actions run.

The source ZIP contains the historical report `fidelity/runs/acceptance-final-20261031/report.json`, recording an overall pass. Its SHA-256 is `c97d92673ed323de94082fb07c44301918f7153178ec39b27f1f6098fc07e1e7`. The verification ZIP contains the additional origin-host run `fidelity/runs/final-delivery-zip-20261031/report.json`, recording a pass after extraction of the final source ZIP; its SHA-256 is `0ee821c2f22dc4c8c7e1921da9c95c1191977d9d504784b4e9b82bef99a7e58c`.

Those runs bind mathematical input snapshot `1dceb00ab137370076aec552c9042c36a497ad067d8c6d4dca82aaa8146b2a3b` and checker/tool snapshot `6c5c3187092f7fab9d449bb2fa8a454c4522ce19066ae82c4be2be397682cb04`. They are origin-host evidence, including fresh project reconstructions with shared pinned dependencies. They do not establish an external receiver's new run or this repository's current CI outcome.

The supplied attribution is reproduced verbatim:

> This Lean 4 formalization was developed by Hangzhou Logicon AI Studio, with AI assistance from OpenAI Codex (GPT-6.1 Sol), under human supervision and review.

The statement's attribution to human supervision and review is the supplied declaration. The automatic review evidence and kernel checks have the distinct scopes described above.
