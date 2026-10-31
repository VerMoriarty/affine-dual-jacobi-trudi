# Continuous verification

The workflow in [verify.yml](../.github/workflows/verify.yml) runs on pushes, pull requests, and manual dispatch. It uses Ubuntu 24.04, Python 3.12.15, Elan 4.2.4, and the frozen Lean `leanprover/lean4:v4.35.0-rc3` toolchain. The Actions are pinned to full commit hashes. The Linux Elan archive is checked against the SHA-256 published on its [official release asset page](https://github.com/leanprover/elan/releases/expanded_assets/v4.2.4).

The workflow has been prepared for GitHub Actions. A successful Linux run must still be observed after publication; this repository does not treat local checks or historical reports as evidence that GitHub CI has passed.

## What is checked

1. `python3 tools/verify.py --prepare-only` verifies the tracked ZIP archives, the source-view manifest, and the extracted delivery manifest, then prepares `build/verification/affine_dual_jt_complete/`.
2. The pinned Lean toolchain is installed. `lake exe cache get` restores the dependencies selected by the unchanged `lake-manifest.json`; the workflow never runs `lake update`.
3. `python3 -m unittest discover -s tests -v` runs the frozen checker's regression tests in the extracted project. These tests and the checker use Python's standard library; no pip packages are required.
4. `python3 tools/verify.py` runs the complete `python3 scripts/check_fidelity.py` audit in that same extracted project. It retains the prepared dependency directory. Only a complete checker run returning zero satisfies this verification.

`formalization/` is the source view used for browsing. CI executes the full frozen delivery extracted from `artifacts/`; its review packets and referenced historical evidence remain inside that delivery. Removing these files from the extracted project would invalidate the evidence checks.

A plain `lake build` is insufficient: its default target does not perform the independent specification and certificate checks, environment export, review validation, exact experiments, semantic mutation checks, or the separate fresh-source and ZIP-extraction reproductions. The complete checker removes the project's existing `.lake/build` and rebuilds its mathematical and fidelity modules. `--static-only`, `--skip-build`, and the publication wrapper's `--check-only` cannot establish complete fresh fidelity verification.

## Cache and resources

The sole GitHub Actions cache path is `build/verification/affine_dual_jt_complete/.lake/packages/`. Its exact key includes the runner operating system, architecture, `lean-toolchain`, and `lake-manifest.json`; there are no prefix fallback keys. Project build outputs, Elan installations, and fidelity reports are not cached. The frozen checker checks every dependency's Git HEAD against the manifest and rejects changes to tracked dependency sources.

Initial preparation needs network access to GitHub, Lean release downloads, and the mathlib cache service. A dependency-cache hit reduces downloads but does not remove the Lean installation or fidelity checks. The pinned mathlib [cache command documentation](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Cache/Main.lean) describes `get`, `clean!`, and `MATHLIB_CACHE_DIR`. After `cache get`, CI runs `cache clean!` to remove downloaded cache archives while retaining the extracted dependency builds.

The local dependency directory occupies about 7 GiB, the fixed Lean toolchain about 2.8 GiB, and project build outputs about 715 MiB. These are local measurements; Linux sizes can differ. GitHub documents only 14 GB of storage for its [standard public Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners). CI therefore removes the unused preinstalled Android SDK from the disposable runner and requires at least 20 GiB free before installing Lean. If the guard fails, the job stops with a disk-space error. Ubuntu 24.04 is selected explicitly to avoid changes to the `ubuntu-latest` label.

The job timeout is 120 minutes. The frozen checker's own default timeout is 3,600 seconds for each subprocess; these are separate limits. Repeated workflow runs for the same branch or pull request cancel the older run. A canceled or interrupted run does not count as a successful verification.

## Reports and permissions

The current audit is named `ci-<GitHub run ID>-<attempt>`. The workflow records the evidence directories that existed immediately before that audit. Its diagnostic artifact contains only newly created runs' reports, input inventories, command stdout/stderr logs, small experiment results, and reproduction manifests, plus the wrapper and regression-test logs. It excludes old runs, large environment exports, dependency caches, and reproduction ZIPs. The artifact is diagnostic evidence, not a complete replacement for the full generated run directory, and is retained for 14 days. Collection and upload are attempted after a failure as well; cancellation, timeout, or infrastructure failure can prevent final artifact upload.

The workflow grants only `contents: read`, disables persisted checkout credentials, uses the `pull_request` event, and does not use repository secrets or `pull_request_target`. Fork pull requests execute in GitHub's pull-request context. No workflow step creates releases, commits, or changes repository contents.

Pinned action releases: [checkout v7.0.1](https://github.com/actions/checkout/releases/tag/v7.0.1), [setup-python v7.1.0](https://github.com/actions/setup-python/releases/tag/v7.1.0), [cache v6.1.0](https://github.com/actions/cache/releases/tag/v6.1.0), and [upload-artifact v7.0.2](https://github.com/actions/upload-artifact/releases/tag/v7.0.2).
