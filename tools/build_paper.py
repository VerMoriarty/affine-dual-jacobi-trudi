#!/usr/bin/env python3
"""Build the standalone publication paper without changing frozen mathematics."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess

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
AI_ORIGINAL = (
    "Artificial intelligence was used to assist in exploring proof strategies "
    "and developing preliminary code for numerical experiments. "
    "All results were independently verified by the authors. "
    "The authors assume responsibility for all content."
)


def block(name, content):
    return f"% GITHUB-EDITION:{name}-BEGIN\n{content}\n% GITHUB-EDITION:{name}-END\n"


def recover_original(text):
    text = re.sub(r"^% GITHUB-EDITION:([A-Z]+)-BEGIN\n.*?^% GITHUB-EDITION:\1-END\n", "", text, flags=re.M | re.S)
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
""" + AI_FIRST + "\n\n" + AI_ORIGINAL + "\n" + r"\medskip"
    text = source.replace("pdfauthor={},", "pdfauthor={" + AUTHOR_META + "},", 1)
    anchor = "via Complementary Minors\n\\end{center}\n"
    assert text.count(anchor) == 1
    text = text.replace(anchor, anchor + block("AUTHORS", AUTHOR_BLOCK), 1)
    anchor = "\\Needspace{30\\baselineskip}\n\\begin{thebibliography}{99}"
    assert text.count(anchor) == 1
    text = text.replace(anchor, block("DISCLOSURE", disclosure) + anchor, 1)
    assert recover_original(text).encode() == source_path.read_bytes()
    assert text.count(AI_FIRST) == text.count(AI_ORIGINAL) == 1
    assert "GitHub URL pending" not in text
    assert not re.search(r"\\(?:input|include|lstinputlisting|bibliography|includegraphics)\s*[\[{]", text)
    (ROOT / "paper").mkdir(exist_ok=True)
    (ROOT / "paper/main.tex").write_text(text, encoding="utf-8")
    if args.compile:
        compiler = shutil.which("pdflatex")
        assert compiler, "pdflatex is required for paper compilation"
        work = ROOT / "build/paper"
        work.mkdir(parents=True, exist_ok=True)
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
        (work / "compilation.json").write_text(json.dumps({"runs": records}, indent=2) + "\n")
    print(json.dumps({"standalone_tex": True, "frozen_math_preserved": True, "code_commit": CODE_COMMIT, "code_permalink": url}))


if __name__ == "__main__":
    main()
