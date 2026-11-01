# Paper: submission manuscript (2026-11-01)

This release archives the 16-page submission manuscript of *Affine Dual Jacobi--Trudi Identities for Classical Hall--Littlewood Polynomials via Complementary Minors*, by Helen W. J. Zhang and Chengdong Zhao.

The manuscript now cites Fischer, Gangl, Gutiérrez and Kumari, [arXiv:2610.08500v1](https://arxiv.org/abs/2610.08500), for their proofs of the six numbered identities for positive width. It describes the difference between their character-expansion route and this manuscript's direct complementary-minor transfer. The manuscript records the authors' account that an earlier version was completed in September 2026 and work on the Lean formalization began on 3 October 2026. These dates describe the research history; they do not establish public priority.

This edition includes the approved AI-use declaration, including `OpenAI's GPT-5.6 Pro`, and continuous exposition within six main sections, with all twelve subsections replaced by prose transitions. Relative to the previously published paper, all 16 result environments, 14 proofs, 64 display-math blocks and three tables are unchanged. The 43 original labels and seven original reference numbers are preserved; the related-work citation is reference [8].

## Formalization baseline

The formalization remains the frozen [`fidelity-20261031`](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/releases/tag/fidelity-20261031) release. The manuscript cites the fixed code commit [`7d58ee5913d67d8036991a5a363260f24f0625bf`](https://github.com/VerMoriarty/affine-dual-jacobi-trudi/tree/7d58ee5913d67d8036991a5a363260f24f0625bf). The frozen Lean sources, dependency locks, source and verification archives, and verification workflow are unchanged. The older release retains its original paper and attachments.

## Downloads and checksums

The four attached files are the complete single-file `main.tex`, `paper.pdf`, the two-file submission package `affine-dual-jt-submission-final.zip`, and `SHA256SUMS.txt`.

| File | SHA-256 |
| --- | --- |
| `main.tex` | `99daa6015835f1fead3e040805d57c2ce0ecaddd163f505f1410fc99c129826a` |
| `paper.pdf` | `ca40a9a3413f01a07b89e0dc3cf07514614e05add4310a5e138419ae657a9302` |
| `affine-dual-jt-submission-final.zip` | `fab58201ebd790fc5958dce2c0144960f6d1a133e6da15e54643bcd320cc89b5` |

The single TeX file compiles without external manuscript files or a bibliography database. It was compiled twice in a fresh directory; all pages were visually checked, and the PDF fonts are embedded. The paper checks and source bindings are recorded in `docs/provenance/PAPER_PUBLICATION.json`. This manuscript revision does not constitute another Lean verification; CI outcomes are available in the workflow attached to the relevant commit.
