#!/usr/bin/env python3
"""Build the standalone publication paper without changing frozen mathematics."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CODE_COMMIT = "7d58ee5913d67d8036991a5a363260f24f0625bf"
REPOSITORY = "https://github.com/VerMoriarty/affine-dual-jacobi-trudi"
AUTHOR_META = "Helen W. J. Zhang and Chengdong Zhao"
AUTHOR_BLOCK = r"""\begin{center}
\large Helen W.~J. Zhang$^{1}$ \qquad Chengdong Zhao$^{2}$\\[6pt]
\small
$^{1}$School of Mathematics, Hunan University\\
\href{mailto:helenzhang@hnu.edu.cn}{\texttt{helenzhang@hnu.edu.cn}}\\[5pt]
$^{2}$School of Mathematics and Statistics, Central South University\\
\href{mailto:cdzhao@csu.edu.cn}{\texttt{cdzhao@csu.edu.cn}}
\end{center}"""
AI_FIRST = (
    "This Lean 4 formalization was developed by Hangzhou Logicon AI Studio, "
    "with AI assistance from OpenAI Codex (GPT-6.1 Sol), "
    "under human supervision and review."
)
AI_RESEARCH = """The idea of adapting Aitken's complementary-minor method for
symmetric-function duality to the identities studied here emerged
through repeated discussions between the authors and OpenAI's
GPT-5.6 Pro. After an initial case had been established, GPT
used this method to derive the corresponding identities for all
the remaining types treated in this paper. AI assistance was also
used to substantially condense and restructure the manuscript and
to develop preliminary code for numerical experiments."""
AI_REVIEW = """The present version was additionally checked using GPT-6.1 Sol.
The authors independently checked the mathematical arguments and
results and take full responsibility for the content of the paper."""
RELATED_WORK = r"""Fischer, Gangl, Guti\'errez and Kumari~\cite{FGGK2026}
have proved these six identities for positive width using character
expansions and the classical dual Jacobi--Trudi identities.
Our proof was obtained independently and proceeds directly from
finite Weyl determinants to affine determinant sums through a
normalized complementary-minor transfer.\footnote{An earlier
version of this manuscript was completed in September 2026.
Work on its Lean formalization began on 3 October 2026.}
"""
RELATED_REFERENCE = r"""\bibitem{FGGK2026}
I.~Fischer, M.~Gangl, \'A.~Guti\'errez and N.~Kumari,
\emph{Character expansions and affine Jacobi--Trudi identities},
arXiv:2610.08500v1 (2026).

"""

# Each editorial change has an exact, unique inverse. The frozen source is
# retained as the input, and mathematical environments are not rewritten.
NARRATIVE_REWRITES = (
    (
        "alternants",
        "\\subsection{Alternants and finite foldings}\n\n",
        "To turn the sign sum \\eqref{eq:signsum} into finite determinant\n"
        "representations, we begin with three alternants.\n",
    ),
    (
        "alternant-preview-deduplication",
        "The finite numerator calculations reduce to three alternants.\n\n"
        "\\begin{lemma}\nWith rows indexed by $1\\le a\\le n$ and columns by $1\\le r\\le n$,",
        "\n\\begin{lemma}\nWith rows indexed by $1\\le a\\le n$ and columns by $1\\le r\\le n$,",
    ),
    (
        "finite-columns",
        "\\subsection{The finite column matrices}\n\n",
        "We now assemble the columns for the seven cases using these foldings.\n",
    ),
    (
        "transfer",
        "\\subsection{The normalized transfer}\n\n",
        "We use the following complementary-minor identity to transfer the\n"
        "finite representations to determinants of order $k$.\n\n",
    ),
    (
        "coefficient-kernels",
        "\\subsection{Three coefficient kernels}\n\n",
        "We begin with the three coefficient kernels and their complementary\nminors.\n",
    ),
    (
        "folding-and-unfolding",
        "\\subsection{Folding and finite unfolding}\n\n"
        "We will fold scalar sequences $b_j(m)$, $m\\in\\Z$, into affine\n"
        "matrices.  The three conventions are\n",
        "For the affine kernels, we fold scalar sequences $b_j(m)$, $m\\in\\Z$,\n"
        "into matrices using the following three conventions.\n",
    ),
    (
        "ordinary-unshifted",
        "\n\n\\subsection{The pair \\texorpdfstring{$C_0$ and $BC$}{C0 and BC}}\n\n",
        "\nWe first treat $C_0$ and $BC$ together.\n\n",
    ),
    (
        "ordinary-shifted",
        "\\subsection{The pair \\texorpdfstring{$B_0$ and $B_-$}{B0 and B-}}\n\n",
        "For $B_0$ and $B_-$, we use the shifted folding and its\n"
        "corresponding reflection.\n\n",
    ),
    (
        "fixed-residue",
        "\n\n\\subsection{The fixed residue in \\texorpdfstring{$C_t$}{Ct}}\n\n",
        "\nWe begin with the fixed residue in the $C_t$ kernel.\n\n",
    ),
    (
        "fixed-center",
        "\\subsection{The fixed center in \\texorpdfstring{$B_+$}{B+}}\n\n"
        "The sequence used here will also supply the adjacent-residue reflection\n"
        "in the next subsection.  For $1\\le j\\le k$, set\n",
        "For $B_+$, the relevant reflection has a fixed center.\n"
        "The sequence below will also supply the adjacent-residue\n"
        "reflection needed for $B_t$.  For $1\\le j\\le k$, set\n",
    ),
    (
        "adjacent-residues",
        "\\subsection{Adjacent residues in \\texorpdfstring{$B_t$}{Bt}}\n\n"
        "This case uses the same coefficient matrix $D^B$ as $B_0$ and $B_-$.\n",
        "Adjacent residues enter in the remaining case $B_t$, which uses the\n"
        "same coefficient matrix $D^B$ as $B_0$ and $B_-$.\n",
    ),
    (
        "empty-rectangle",
        "\\subsection{The normalized empty rectangle}\n\n",
        "We first determine the normalized empty-rectangle values directly\n"
        "from the finite Weyl representation.\n\n",
    ),
    (
        "classical-specialization",
        "\\subsection{The specialization \\texorpdfstring{$t=0$}{t=0}}\n\n"
        "The classical rectangular dual Jacobi--Trudi formulas are recovered in\n"
        "three finite foldings.  ",
        "At $t=0$, the three finite foldings recover the classical rectangular\n"
        "dual Jacobi--Trudi formulas.  ",
    ),
)


def apply_narrative_rewrites(text):
    for name, before, after in NARRATIVE_REWRITES:
        assert text.count(before) == 1, f"Editorial input anchor changed: {name}"
        text = text.replace(before, after, 1)
    assert not re.search(r"\\(?:subsection|subsubsection|paragraph|subparagraph)\b", text)
    assert not re.search(r"\bsubsection\b", text, re.I)
    return text


def block(name, content):
    return f"% GITHUB-EDITION:{name}-BEGIN\n{content}\n% GITHUB-EDITION:{name}-END\n"


def recover_original(text):
    text = re.sub(r"^% GITHUB-EDITION:([A-Z]+)-BEGIN\n.*?^% GITHUB-EDITION:\1-END\n", "", text, flags=re.M | re.S)
    for name, before, after in reversed(NARRATIVE_REWRITES):
        assert text.count(after) == 1, f"Editorial inverse anchor changed: {name}"
        text = text.replace(after, before, 1)
    return text.replace("pdfauthor={" + AUTHOR_META + "},", "pdfauthor={},", 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compile", action="store_true", help="Compile with pdflatex twice")
    args = parser.parse_args()
    source_path = ROOT / "formalization/source.tex"
    source = source_path.read_text(encoding="utf-8")
    assert hashlib.sha256(source_path.read_bytes()).hexdigest() == "4141e8fa7c8fc8d7499b1d10bb77fcc1440d229169f44610709ebaf8968a5a19"
    assert re.fullmatch(r"[0-9a-f]{40}", CODE_COMMIT)
    url = REPOSITORY + "/tree/" + CODE_COMMIT
    disclosure = r"""\medskip
\noindent\textbf{Lean formalization.}
Theorems~A and~B, together with the auxiliary results listed in the
accompanying code, have been formalized in Lean~4. The source code,
theorem correspondence, and verification instructions are available at
\url{""" + url + r"""}.

\Needspace{12\baselineskip}
\medskip
\noindent\textbf{AI use declaration.}
""" + AI_FIRST + "\n\n" + AI_RESEARCH + "\n\n" + AI_REVIEW + "\n" + r"\medskip"
    text = apply_narrative_rewrites(source)
    text = text.replace("pdfauthor={},", "pdfauthor={" + AUTHOR_META + "},", 1)
    anchor = "via Complementary Minors\n\\end{center}\n"
    assert text.count(anchor) == 1
    text = text.replace(anchor, anchor + block("AUTHORS", AUTHOR_BLOCK), 1)
    anchor = "For $x=(x_1,\\ldots,x_n)$, define\n"
    assert text.count(anchor) == 1
    text = text.replace(anchor, block("RELATEDWORK", RELATED_WORK) + anchor, 1)
    anchor = "\\Needspace{30\\baselineskip}\n\\begin{thebibliography}{99}"
    assert text.count(anchor) == 1
    text = text.replace(anchor, block("DISCLOSURE", disclosure) + anchor, 1)
    anchor = "\\end{thebibliography}"
    assert text.count(anchor) == 1
    text = text.replace(anchor, block("RELATEDREFERENCE", RELATED_REFERENCE) + anchor, 1)
    assert recover_original(text).encode() == source_path.read_bytes()
    assert all(text.count(paragraph) == 1 for paragraph in (AI_FIRST, AI_RESEARCH, AI_REVIEW))
    assert text.count(RELATED_WORK) == text.count(RELATED_REFERENCE) == 1
    assert "OpenAI's GPT-5.6 Pro" in " ".join(text.split())
    assert "GPT-5.6 Thinking" not in text
    assert "GitHub URL pending" not in text
    assert not re.search(r"\\(?:input|include|lstinputlisting|bibliography|includegraphics)\s*[\[{]", text)
    (ROOT / "paper").mkdir(exist_ok=True)
    (ROOT / "paper/main.tex").write_text(text, encoding="utf-8")
    if args.compile:
        compiler = shutil.which("pdflatex")
        assert compiler, "pdflatex is required for paper compilation"
        work_root = ROOT / "build/paper"
        work_root.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="standalone-", dir=work_root))
        shutil.copyfile(ROOT / "paper/main.tex", work / "main.tex")
        records = []
        for number in (1, 2):
            command = [compiler, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "main.tex"]
            proc = subprocess.run(command, cwd=work, capture_output=True, text=True, timeout=120)
            (work / f"pass-{number}.log").write_text(proc.stdout + proc.stderr)
            records.append({"command": command, "exit_code": proc.returncode})
            assert proc.returncode == 0, f"Paper compilation failed; see {work}"
        log = (work / "main.log").read_text()
        assert not any(s in log for s in ["Overfull", "Underfull", "Missing character", "undefined references", "LaTeX Warning", "! LaTeX Error"])
        shutil.copyfile(work / "main.pdf", ROOT / "paper/paper.pdf")
        (work / "compilation.json").write_text(json.dumps({"runs": records, "clean_directory": True}, indent=2) + "\n")
    print(json.dumps({"standalone_tex": True, "frozen_math_preserved": True, "code_commit": CODE_COMMIT, "code_permalink": url}))


if __name__ == "__main__":
    main()
