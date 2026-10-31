"""Input isolation is an acceptance requirement, not merely a prompt preference."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from fidelity.prepare_review import prepare


class ReviewPacketsTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="review-packet-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name, value in {
            "AffineDualJT.lean": "import AffineDualJT.Basic\n",
            "AffineDualJT/Basic.lean": "def exampleObject := 1\n",
            "FidelityLean/Spec.lean": "import Mathlib\n",
            "fidelity/inputs/authoritative.pdf": "paper-only-input",
            "fidelity/inputs/authoritative.txt": "paper-only-input",
            "fidelity/specs/paper_a.json": "{}",
            "fidelity/specs/paper_b.json": "{}",
            "fidelity/specs/canonical_math.json": "{}",
            "fidelity/canonical_claims.json": "{}",
            "fidelity/protocol.json": "{}",
            "fidelity/reviews/lean_reverse.json": '{"role":"lean_reverse"}',
            "fidelity/certificates.json": '{"entries":[]}',
            "fidelity/specs/zero_parameter_addendum.json": '{}',
        }.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(value)
        path = self.root / "fidelity/runs/export/environment.json"
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps({"decls": [
            {"name": "AffineDualJT.object", "module": "AffineDualJT.Basic", "type": "Nat"},
            {"name": "Fidelity.Spec.paperGoal", "module": "FidelityLean.Spec", "type": "Prop"}]}))
        self.environment = path.relative_to(self.root).as_posix()

    def test_reverse_translator_cannot_see_paper_or_specification(self):
        packet = prepare(self.root, "lean_reverse", self.environment)
        data = json.loads((packet / "implementation_environment.json").read_text())
        self.assertEqual([d["name"] for d in data["decls"]], ["AffineDualJT.object"])
        self.assertFalse((packet / "inputs").exists())
        self.assertFalse(any(p.suffix == ".pdf" for p in packet.rglob("*")))

    def test_semantic_packet_contains_both_sides_and_never_a_verdict(self):
        packet = prepare(self.root, "semantic_1", self.environment)
        self.assertTrue((packet / "inputs/fidelity/inputs/authoritative.pdf").is_file())
        self.assertTrue((packet / "inputs/fidelity/specs/canonical_math.json").is_file())
        self.assertTrue((packet / "environment.json").is_file())
        self.assertFalse(json.loads((packet / "manifest.json").read_text())["verdict_created"])

    def test_paper_packet_contains_only_authoritative_paper(self):
        packet = prepare(self.root, "paper_a")
        inputs = json.loads((packet / "manifest.json").read_text())["allowed_copied_inputs"]
        self.assertEqual({entry["source"] for entry in inputs}, {
            "fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt"})

    def test_environment_traversal_and_missing_environment_are_rejected(self):
        with self.assertRaises(ValueError):
            prepare(self.root, "semantic_1")
        with self.assertRaises(ValueError):
            prepare(self.root, "lean_reverse", "../../outside.json")


if __name__ == "__main__":
    unittest.main()
