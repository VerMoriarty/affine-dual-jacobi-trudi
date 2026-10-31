"""Meaningful rejection tests for the fidelity acceptance boundary.

Run with: python3 -m unittest discover -s tests -v
These fixtures model evidence formats; they do not certify the real project.
"""

from __future__ import annotations

import copy
from fractions import Fraction
import json
import os
import re
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from fidelity import checks, metadata
from fidelity.common import (DIMENSIONS, EvidenceError, canonical_digest,
                             code_only, digest, digest_bytes, input_snapshot,
                             mathematical_sources, portable_paths, read_json, save_json)
from fidelity.experiments import Case, emit_report, rational
from fidelity.runner import Runner


class EvidenceFixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fidelity-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        files = {
            "README.md": "Toy evidence fixture; no real paper acceptance.\n",
            "tests/test_portability.py": "# Included test source\n",
            "AffineDualJT.lean": "import AffineDualJT.Basic\n",
            "AffineDualJT/Basic.lean": "namespace AffineDualJT\ntheorem one : True := True.intro\nend AffineDualJT\n",
            "lean-toolchain": "leanprover/lean4:v4.35.0-rc3\n",
            "lakefile.toml": 'name = "test"\n',
            "lake-manifest.json": '{"packages": []}\n',
            "source.tex": "authoritative math tex",
            "fidelity/inputs/reference.tex": "authoritative math tex",
            "source.pdf": "packaged pdf",
            "fidelity/inputs/packaged.pdf": "packaged pdf",
            "fidelity/inputs/authoritative.pdf": "authoritative pdf",
            "fidelity/inputs/authoritative.txt": "authoritative extracted text",
            "fidelity/inputs/original-source.zip": "pinned original archive",
            "scripts/check_fidelity.py": "# isolated fixture, never executed\n",
            "FidelityLean/Export.lean": "import Lean\n",
            "FidelityLean/Certificates.lean": "import AffineDualJT\n",
            "FidelityLean/Spec.lean": "import Mathlib\n",
        }
        for name, data in files.items():
            self.write(name, data)
        self.write_json("fidelity/protocol.json", {"schema_version": 1,
                        "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"]})
        self.write_json("fidelity/baseline.json", {
            "schema_version": 1, "authority": "authoritative_pdf",
            "inputs": {key: {"path": aliases[0], "sha256": digest(self.root / aliases[0])}
                       for key, aliases in checks.BASELINE_FILES.items()}})
        for side in ("paper_a", "paper_b"):
            self.write_json(f"fidelity/specs/{side}.json", {
                "schema_version": 1, "role": f"paper_spec_{side[-1]}",
                "inputs": [{"path": "fidelity/inputs/authoritative.pdf",
                            "sha256": digest(self.root / "fidelity/inputs/authoritative.pdf")}],
                "claims": [{"id": f"{side}.one", "kind": "statement", "container": "Theorem 1",
                            "page": 1, "locator": "Theorem 1, sentence 1", "statement": "True",
                            "assumptions": [], "objects": [], "route": [], "edge_cases": []}]})
        self.claims = {"claim.one": {"id": "claim.one", "paper_a": ["paper_a.one"],
                                    "paper_b": ["paper_b.one"], "declarations": ["AffineDualJT.one"], "container": "A",
                                    "mapping_relation": "equivalent", "source_evidence": [{
                                        "path": "fidelity/inputs/authoritative.pdf",
                                        "sha256": digest(self.root / "fidelity/inputs/authoritative.pdf"),
                                        "locator": "Theorem 1, page 1"}]}}
        self.write_json("fidelity/canonical_claims.json", {"schema_version": 1,
                                                          "claims": list(self.claims.values())})
        self.write_json("fidelity/experiments.json", {"schema_version": 1, "required_cases": ["rank_one"]})
        self.write_json("fidelity/issues/registry.json", {"schema_version": 1, "issues": []})
        declaration = {"name": "AffineDualJT.one", "module": "AffineDualJT.Basic", "type": "True",
                       "type_hash": digest_bytes(b"True"), "type_constants": ["True"],
                       "value_constants": ["True.intro"], "axioms": [], "kind": "theorem", "value_available": True}
        self.environment = {"decls": [declaration], "run_id": "review-export"}
        self.env = {declaration["name"]: declaration}
        self.environment_path = "fidelity/runs/review-export/environment.json"
        self.write_json(self.environment_path, self.environment)
        self.inputs = input_snapshot(self.root)

    def write(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data, encoding="utf-8")
        return path

    def write_json(self, name, data):
        path = self.root / name
        save_json(path, data)
        return path

    def create_reviews(self):
        from fidelity.prepare_review import prepare
        for name, value in (("fidelity/specs/canonical_math.json", {"schema_version": 1, "claims": list(self.claims.values())}),
                            ("fidelity/certificates.json", {"schema_version": 1, "entries": []}),
                            ("fidelity/specs/zero_parameter_addendum.json", {"schema_version": 1, "statements": []})):
            if not (self.root / name).is_file():
                self.write_json(name, value)
        reverse_path = "fidelity/reviews/lean_reverse.json"
        if not (self.root / reverse_path).is_file():
            packet_path = "fidelity/packets/fixture-blind/implementation_environment.json"
            self.write_json(packet_path, {"schema_version": 1,
                "original_environment_sha256": digest(self.root / self.environment_path), "decls": self.environment["decls"]})
            decl = self.environment["decls"][0]
            self.write_json(reverse_path, {"schema_version": 1, "role": "lean_reverse",
                "reviewer": {"id": "toy-blind-reviewer", "independent": True},
                "inputs": {self.environment_path: digest(self.root / self.environment_path), packet_path: digest(self.root / packet_path)},
                "inspected_inputs": [{"path": packet_path, "sha256": digest(self.root / packet_path), "read": True}],
                "declarations": [{"name": decl["name"], "module": decl["module"], "kind": decl["kind"],
                    "full_type": decl["type"], "full_type_sha256": digest_bytes(decl["type"].encode()),
                    "axioms": decl["axioms"], "value_available": decl["value_available"],
                    "project_type_dependencies": [], "project_value_dependencies": []}],
                "objects": [], "coverage": {"all_decl_ids_indexed": [decl["name"]]},
                "module_index": {decl["module"]: [decl["name"]]}})
        self.inputs = input_snapshot(self.root)
        evidence = [{"path": name, "sha256": digest(self.root / name), "locator": locator}
                    for name, locator in (("fidelity/specs/paper_a.json", "paper_a.one"),
                                          (self.environment_path, "AffineDualJT.one.type"))]
        judgment = {"status": "pass", "rationale": "The exported proposition and the atom both state True.",
                    "evidence": evidence}
        for identity, kind in (("reviewer-one", "semantic"), ("reviewer-two", "semantic"), ("route-reviewer", "route")):
            role = "route" if kind == "route" else ("semantic_1" if identity == "reviewer-one" else "semantic_2")
            packet = prepare(self.root, role, self.environment_path)
            manifest = read_json(packet / "manifest.json")
            inspected = [{"path": (packet / "manifest.json").relative_to(self.root).as_posix(),
                          "sha256": digest(packet / "manifest.json"), "read": True}]
            inspected += [{"path": (packet / item["packet"]).relative_to(self.root).as_posix(),
                           "sha256": digest(packet / item["packet"]), "read": True}
                          for item in manifest["allowed_copied_inputs"]]
            claim = {"id": "claim.one", "open_issues": []}
            if kind == "semantic":
                claim["dimensions"] = {key: copy.deepcopy(judgment) for key in DIMENSIONS}
            else:
                claim.update(route=copy.deepcopy(judgment), dependency_anchors=["True.intro"])
            self.write_json(f"fidelity/reviews/{identity}.json", {
                "schema_version": 1, "kind": kind,
                "reviewer": {"id": identity, "independent": True, "fresh_context": True},
                "packet_manifest": {"path": (packet / "manifest.json").relative_to(self.root).as_posix(),
                                    "sha256": digest(packet / "manifest.json")},
                "inspected_inputs": inspected,
                "inputs": manifest["bound_input_hashes"], "claims": [claim], "open_issues": []})

    def validate_reviews(self):
        return checks.reviews(self.root, input_snapshot(self.root), self.claims,
                              self.env, canonical_digest(self.environment["decls"]), validated_metadata_roles={"lean_reverse"})


class ValidatorTests(EvidenceFixture):
    def test_missing_absolute_authoritative_input_has_unique_hashed_portable_alias(self):
        for side in ("paper_a", "paper_b"):
            path = self.root / f"fidelity/specs/{side}.json"
            data = read_json(path)
            data["inputs"][0]["path"] = "/not/a/receivers/workspace/fidelity/inputs/authoritative.pdf"
            save_json(path, data)
        self.assertEqual(len(checks.specifications(self.root)["paper_a"]), 1)
        self.write("fidelity/inputs/duplicate/authoritative.pdf", "authoritative pdf")
        with self.assertRaisesRegex(EvidenceError, "ambiguous portable"):
            checks.specifications(self.root)

    def test_missing_arbitrary_absolute_input_has_no_portable_alias(self):
        with self.assertRaisesRegex(EvidenceError, "no portable alias"):
            checks.source_input(self.root, "/missing/elsewhere/source.tex", digest(self.root / "source.tex"))

    def test_existing_absolute_stale_input_is_not_rebound_to_good_copy(self):
        stale = self.write("elsewhere/authoritative.pdf", "different paper")
        with self.assertRaisesRegex(EvidenceError, "Stale source"):
            checks.source_input(self.root, str(stale), digest(self.root / "fidelity/inputs/authoritative.pdf"))

    def test_original_source_archive_is_required_and_resolved_against_root(self):
        self.assertTrue(checks.baseline(self.root)["source_archive_present"])
        path = self.root / "fidelity/inputs/original-source.zip"
        path.unlink()
        with self.assertRaisesRegex(EvidenceError, "Missing regular project file"):
            checks.baseline(self.root)
        path.write_bytes(b"replaced original archive")
        with self.assertRaisesRegex(EvidenceError, "baseline input"):
            checks.baseline(self.root)

    def test_frozen_mathematics_allows_only_added_declarations(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        data["claims"][0].update(statement="True", assumptions=[], route=[])
        frozen = copy.deepcopy(data)
        frozen["claims"][0]["declarations"] = []
        path = self.write_json("fidelity/specs/canonical_math.json", frozen)
        frozen_hash = digest(path)
        data["mapping_provenance"] = {"coordinator": "test"}
        data["claims"][0]["declarations"].append("AffineDualJT.another_mapping")
        self.write_json("fidelity/canonical_claims.json", data)
        checks.canonical_coverage(self.root, checks.specifications(self.root), frozen_sha256=frozen_hash)
        for field, changed in (("statement", "False"), ("assumptions", ["False"]), ("route", ["shortcut"])):
            with self.subTest(field=field):
                mutated = copy.deepcopy(data)
                mutated["claims"][0][field] = changed
                self.write_json("fidelity/canonical_claims.json", mutated)
                with self.assertRaisesRegex(EvidenceError, "Frozen independent canonical mathematics changed"):
                    checks.canonical_coverage(self.root, checks.specifications(self.root), frozen_sha256=frozen_hash)

    def test_mutating_frozen_copy_together_with_mapping_does_not_bypass_pin(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        path = self.write_json("fidelity/specs/canonical_math.json", data)
        pin = digest(path)
        data["claims"][0]["statement"] = "redefined target"
        self.write_json("fidelity/specs/canonical_math.json", data)
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "hash changed"):
            checks.canonical_coverage(self.root, checks.specifications(self.root), frozen_sha256=pin)

    def test_pure_specification_source_and_environment_firewall(self):
        self.write("FidelityLean/ZeroParameterSpec.lean", "import FidelityLean.Spec\n")
        self.assertEqual(len(checks.pure_spec_sources(self.root)), 2)
        self.write("FidelityLean/Spec.lean", "import Mathlib\nimport AffineDualJT\n")
        with self.assertRaisesRegex(EvidenceError, "import firewall"):
            checks.pure_spec_sources(self.root)
        env = {"Fidelity.Spec.Statement": {"module": "FidelityLean.Spec",
               "type_constants": ["AffineDualJT.one"], "value_constants": []}}
        with self.assertRaisesRegex(EvidenceError, "depends on implementation"):
            checks.pure_spec_environment(env)
        env["Fidelity.Spec.Statement"].update(module="FidelityLean.ZeroParameterSpec",
            type_constants=[], value_constants=["Fidelity.Certificate.certificate"])
        with self.assertRaisesRegex(EvidenceError, "depends on implementation"):
            checks.pure_spec_environment(env)

    def certificate_fixture(self):
        env = copy.deepcopy(self.env)
        env["Fidelity.Spec.Statement"] = {"module": "FidelityLean.Spec", "kind": "definition",
            "type_constants": ["Prop"], "value_constants": []}
        env["Fidelity.Certificate.one"] = {"module": "FidelityLean.MainCertificates", "kind": "theorem",
            "type_constants": ["Fidelity.Spec.Statement"], "value_constants": ["AffineDualJT.one"]}
        data = {"schema_version": 1, "entries": [{"id": "cert.one", "container": "A",
            "specification": "Fidelity.Spec.Statement", "certificate": "Fidelity.Certificate.one", "claims": ["claim.one"]}]}
        self.write_json("fidelity/certificates.json", data)
        return env, data

    def test_certificates_require_all_source_containers_and_real_theorem_type_anchor(self):
        env, _ = self.certificate_fixture()
        result = checks.certificates(self.root, env, self.claims, required_containers=frozenset({"A"}))
        self.assertEqual(result["per_claim"]["claim.one"], ["Fidelity.Certificate.one"])
        with self.assertRaisesRegex(EvidenceError, "Missing independent certificate source containers"):
            checks.certificates(self.root, env, self.claims)
        for field, value, message in (("kind", "definition", "compiled theorem"),
                                      ("type_constants", [], "omits its independent specification")):
            with self.subTest(field=field):
                mutated = copy.deepcopy(env)
                mutated["Fidelity.Certificate.one"][field] = value
                with self.assertRaisesRegex(EvidenceError, message):
                    checks.certificates(self.root, mutated, self.claims, required_containers=frozenset({"A"}))

    def test_certificate_claims_and_independent_spec_module_are_verified(self):
        env, data = self.certificate_fixture()
        env["Fidelity.Spec.Statement"]["module"] = "AffineDualJT.Basic"
        with self.assertRaisesRegex(EvidenceError, "independently defined"):
            checks.certificates(self.root, env, self.claims, required_containers=frozenset({"A"}))
        env["Fidelity.Spec.Statement"]["module"] = "FidelityLean.ZeroParameterSpec"
        checks.certificates(self.root, env, self.claims, required_containers=frozenset({"A"}))
        data["entries"][0]["claims"] = ["invented.claim"]
        self.write_json("fidelity/certificates.json", data)
        with self.assertRaisesRegex(EvidenceError, "Unknown canonical certificate claim"):
            checks.certificates(self.root, env, self.claims, required_containers=frozenset({"A"}))

    def mutation_fixture(self):
        from fidelity.semantic_mutations import FIXTURES
        cases = []
        for key, (source, certificate) in FIXTURES.items():
            theorem = re.search(r"#print axioms\s+(\w+)", source).group(1)
            cases.append({"id": key, "status": "pass", "fixture_source": source,
                "independent_certificate": certificate, "fixture_sha256": digest_bytes(source.encode()),
                "fixture_compilation_exit_code": 0, "certificate_exit_code": 1,
                "fixture_stdout": f"'{theorem}' does not depend on any axioms\n", "fixture_stderr": "",
                "certificate_stdout": "error: type mismatch", "certificate_stderr": ""})
        return {"schema_version": 1, "supporting_only": True, "lean_version": "Lean (version 4.35.0-rc3, test)",
                "status": "pass", "cases": cases}

    def test_semantic_mutations_recompute_exit_diagnostic_axioms_and_fixed_version(self):
        data = self.mutation_fixture()
        self.assertEqual(checks.semantic_mutations(self.root, data)["cases"], 3)
        mutations = [("fixture_compilation_exit_code", 1), ("certificate_exit_code", 0),
                     ("fixture_stdout", "depends on axioms [sorryAx]"),
                     ("certificate_stdout", "unrelated network failure"), ("fixture_source", "changed target")]
        for field, value in mutations:
            with self.subTest(field=field):
                mutated = copy.deepcopy(data)
                mutated["cases"][0][field] = value
                with self.assertRaises(EvidenceError):
                    checks.semantic_mutations(self.root, mutated)
        data["lean_version"] = "Lean (version 4.33.0, test)"
        with self.assertRaisesRegex(EvidenceError, "different Lean version"):
            checks.semantic_mutations(self.root, data)

    def test_route_check_uses_actual_proof_and_cannot_be_injected_through_mapping(self):
        from fidelity.route_dependencies import validate
        data = {"schema_version": 1, "rules": [{"claim": "claim.one", "proof_entrypoint": "AffineDualJT.one",
            "required_dependencies": ["AffineDualJT.checkpoint"], "source_evidence": self.claims["claim.one"]["source_evidence"]}]}
        self.write_json("fidelity/route_requirements.json", data)
        claims = copy.deepcopy(self.claims)
        claims["claim.one"]["declarations"].append("AffineDualJT.checkpoint")
        with self.assertRaisesRegex(EvidenceError, "Proof route changed"):
            validate(self.root, self.env, claims)
        env = copy.deepcopy(self.env)
        env["AffineDualJT.one"]["value_constants"].append("AffineDualJT.checkpoint")
        env["AffineDualJT.checkpoint"] = {"kind": "theorem", "type_constants": [], "value_constants": []}
        self.assertEqual(len(validate(self.root, env, self.claims)["rules"]), 1)
    def test_complete_static_evidence_is_structurally_valid(self):
        self.assertEqual(len(checks.baseline(self.root)["verified_inputs"]), 9)
        specs = checks.specifications(self.root)
        self.assertEqual(len(checks.canonical_coverage(self.root, specs)["claims"]), 1)
        audit = checks.source_audit(self.root)
        self.assertEqual(len(checks.environment(self.environment, self.claims,
                                                audit["modules_with_declarations"])), 1)

    def test_missing_review_evidence_cannot_pass(self):
        with self.assertRaisesRegex(EvidenceError, "Missing independent"):
            self.validate_reviews()

    def test_changed_authoritative_source_cannot_pass(self):
        self.write("fidelity/inputs/authoritative.pdf", "mutated mathematical paper")
        with self.assertRaisesRegex(EvidenceError, "baseline input"):
            checks.baseline(self.root)
        with self.assertRaisesRegex(EvidenceError, "Stale paper_a"):
            checks.specifications(self.root)

    def test_extra_axiom_in_non_headline_declaration_is_rejected(self):
        hidden = copy.deepcopy(self.environment["decls"][0])
        hidden.update(name="AffineDualJT.hidden", axioms=["propext", "Lean.ofReduceBool"])
        data = {"decls": [*self.environment["decls"], hidden]}
        with self.assertRaisesRegex(EvidenceError, "Forbidden transitive axioms.*hidden"):
            checks.environment(data, self.claims, ["AffineDualJT.Basic"])

    def test_missing_intermediate_project_declaration_is_rejected(self):
        data = copy.deepcopy(self.environment)
        data["decls"][0]["value_constants"].append("AffineDualJT.unexported")
        with self.assertRaisesRegex(EvidenceError, "truncated project closure"):
            checks.environment(data, self.claims, ["AffineDualJT.Basic"])

    def test_type_hash_is_recomputed(self):
        data = copy.deepcopy(self.environment)
        data["decls"][0]["type"] = "False"
        with self.assertRaisesRegex(EvidenceError, "type hash"):
            checks.environment(data, self.claims, ["AffineDualJT.Basic"])

    def test_missing_exported_module_is_rejected(self):
        with self.assertRaisesRegex(EvidenceError, "omits mathematical modules"):
            checks.environment(self.environment, self.claims, ["AffineDualJT.Missing"])

    def test_root_source_is_scanned_and_nested_comments_are_ignored(self):
        self.write("AffineDualJT.lean", "import AffineDualJT.Basic\n/- sorry /- axiom -/ admit -/\n#check \"unsafe sorry\"\n")
        checks.source_audit(self.root)
        self.write("AffineDualJT.lean", "theorem bad : False := by sorry\n")
        with self.assertRaisesRegex(EvidenceError, "Source audit rejected"):
            checks.source_audit(self.root)

    def test_missing_atomic_claim_is_rejected(self):
        specs = checks.specifications(self.root)
        specs["paper_b"]["paper_b.missing"] = {"id": "paper_b.missing"}
        with self.assertRaisesRegex(EvidenceError, "coverage is incomplete"):
            checks.canonical_coverage(self.root, specs)

    def test_duplicate_atomic_use_within_one_claim_is_rejected(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        data["claims"][0]["paper_a"].append("paper_a.one")
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "Duplicate atom within canonical claim"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_cross_claim_atomic_reuse_is_allowed_and_counted_once_for_coverage(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        second = copy.deepcopy(data["claims"][0])
        second.update(id="claim.component", mapping_relation="component_of")
        data["claims"].append(second)
        self.write_json("fidelity/canonical_claims.json", data)
        result = checks.canonical_coverage(self.root, checks.specifications(self.root))
        self.assertEqual(len(result["claims"]), 2)
        for side in ("paper_a", "paper_b"):
            self.assertEqual(result["coverage"][side]["covered"], 1)
            self.assertEqual(result["coverage"][side]["reference_count"], 2)
            self.assertEqual(result["coverage"][side]["reused_atoms"], [f"{side}.one"])

    def test_mapping_relation_and_hashed_original_source_evidence_are_required(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        del data["claims"][0]["mapping_relation"]
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "mapping_relation"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))
        data["claims"][0]["mapping_relation"] = "equivalent"
        data["claims"][0]["source_evidence"] = []
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "nonempty list"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_source_only_mapping_can_have_one_empty_side_with_original_evidence(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        second = copy.deepcopy(data["claims"][0])
        second.update(id="claim.source_only", paper_a=[], mapping_relation="source_only")
        data["claims"].append(second)
        self.write_json("fidelity/canonical_claims.json", data)
        result = checks.canonical_coverage(self.root, checks.specifications(self.root))
        self.assertEqual(result["coverage"]["paper_a"]["covered"], 1)
        self.assertEqual(result["coverage"]["paper_b"]["reference_count"], 2)
        second["mapping_relation"] = "equivalent"
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "empty mapping side requires source_only"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_two_empty_mapping_sides_are_rejected(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        second = copy.deepcopy(data["claims"][0])
        second.update(id="claim.no_atoms", paper_a=[], paper_b=[], mapping_relation="source_only")
        data["claims"].append(second)
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "no source atoms"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_unknown_atom_is_rejected_even_with_original_source_evidence(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        data["claims"][0]["paper_a"].append("paper_a.invented")
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "coverage is incomplete or unknown"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_specification_alone_does_not_replace_original_source_evidence(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        path = "fidelity/specs/paper_a.json"
        data["claims"][0]["source_evidence"] = [{"path": path, "sha256": digest(self.root / path),
                                                   "locator": "paper_a.one"}]
        self.write_json("fidelity/canonical_claims.json", data)
        with self.assertRaisesRegex(EvidenceError, "direct original-paper evidence"):
            checks.canonical_coverage(self.root, checks.specifications(self.root))

    def test_two_semantic_and_route_reviews_are_required(self):
        self.create_reviews()
        self.assertEqual(len(self.validate_reviews()["semantic"]), 2)
        (self.root / "fidelity/reviews/reviewer-two.json").unlink()
        with self.assertRaisesRegex(EvidenceError, "Two distinct"):
            self.validate_reviews()

    def test_review_binds_content_even_when_run_metadata_differs(self):
        self.create_reviews()
        current = copy.deepcopy(self.environment)
        current["run_id"] = "fresh-final-run"
        self.assertEqual(len(checks.reviews(self.root, self.inputs, self.claims, self.env,
                                           canonical_digest(current["decls"]), validated_metadata_roles={"lean_reverse"})["route"]), 1)

    def test_source_mutation_invalidates_existing_reviews(self):
        self.create_reviews()
        self.write("AffineDualJT/Basic.lean", "theorem one : False := by contradiction\n")
        with self.assertRaisesRegex(EvidenceError, "Stale or missing review input"):
            self.validate_reviews()

    def test_malformed_review_dimension_is_rejected(self):
        self.create_reviews()
        path = self.root / "fidelity/reviews/reviewer-one.json"
        data = read_json(path)
        del data["claims"][0]["dimensions"]["nonvacuity"]
        save_json(path, data)
        with self.assertRaisesRegex(EvidenceError, "all five semantic dimensions"):
            self.validate_reviews()

    def test_pass_label_without_evidence_is_rejected(self):
        self.create_reviews()
        path = self.root / "fidelity/reviews/reviewer-one.json"
        data = read_json(path)
        data["claims"][0]["dimensions"]["objects"]["evidence"] = []
        save_json(path, data)
        with self.assertRaisesRegex(EvidenceError, "nonempty list"):
            self.validate_reviews()

    def test_open_issue_prevents_acceptance(self):
        self.create_reviews()
        path = self.root / "fidelity/reviews/route-reviewer.json"
        data = read_json(path)
        data["open_issues"] = ["Proof route differs from paper"]
        save_json(path, data)
        with self.assertRaisesRegex(EvidenceError, "Unresolved"):
            self.validate_reviews()

    def test_route_anchor_must_be_real_dependency(self):
        self.create_reviews()
        path = self.root / "fidelity/reviews/route-reviewer.json"
        data = read_json(path)
        data["claims"][0]["dependency_anchors"] = ["AffineDualJT.unrelated_lemma"]
        save_json(path, data)
        with self.assertRaisesRegex(EvidenceError, "actual dependency closure"):
            self.validate_reviews()

    def test_duplicate_json_keys_are_not_accepted(self):
        path = self.write("fidelity/reviews/invalid.json", '{"kind":"route","kind":"semantic"}')
        with self.assertRaisesRegex(EvidenceError, "Duplicate JSON key"):
            read_json(path)

    def test_wrong_exact_result_is_rejected_despite_pass_label(self):
        output = {"schema_version": 1, "arithmetic": "exact", "open_issues": [],
                  "cases": [{"id": "rank_one", "claims": ["claim.one"], "status": "pass",
                             "comparisons": [{"left": "1/3", "right": "2/3"}]}]}
        with self.assertRaisesRegex(EvidenceError, "disagrees"):
            checks.experiments(self.root, output, self.claims)
        output["cases"][0]["comparisons"][0] = {"left": 0.5, "right": 0.5}
        with self.assertRaisesRegex(EvidenceError, "Non-exact"):
            checks.experiments(self.root, output, self.claims)

    def test_exact_case_helper_never_supplies_default_success(self):
        case = Case("rank_one", ["claim.one"])
        output = self.root / "case.json"
        self.assertEqual(emit_report(output, [case]), 1)
        case.compare(Fraction(1, 3) + Fraction(1, 6), Fraction(1, 2))
        self.assertEqual(emit_report(output, [case]), 0)
        self.assertEqual(checks.experiments(self.root, read_json(output), self.claims)["exact_comparisons"], 1)
        with self.assertRaises(EvidenceError):
            rational(0.5)

    def test_casefold_path_collision_is_rejected_for_portable_packages(self):
        with self.assertRaisesRegex(EvidenceError, "path collision"):
            portable_paths(["Fidelity/Spec.lean", "fidelity/spec.lean"])
        portable_paths(["FidelityLean/Spec.lean", "fidelity/specs/paper_a.json"])

    def test_current_issue_registry_is_required(self):
        (self.root / "fidelity/issues/registry.json").unlink()
        with self.assertRaisesRegex(EvidenceError, "Missing evidence"):
            checks.issue_registry(self.root)

    def test_historical_issue_cannot_be_omitted_from_current_registry(self):
        self.write_json("fidelity/issues/raw-review.json", {"issues": [{"id": "ISSUE-1", "status": "open"}]})
        with self.assertRaisesRegex(EvidenceError, "omitted from current registry"):
            checks.issue_registry(self.root)

    def test_historical_open_issue_can_be_resolved_by_current_hashed_evidence(self):
        self.write_json("fidelity/issues/raw-review.json", {"issues": [{"id": "ISSUE-1", "status": "open"}]})
        self.write_json("fidelity/issues/registry.json", {
            "schema_version": 1, "issues": [{"id": "ISSUE-1", "status": "resolved", "evidence": [
                {"path": "AffineDualJT/Basic.lean", "sha256": digest(self.root / "AffineDualJT/Basic.lean"),
                 "locator": "AffineDualJT.one"}]}]})
        self.assertEqual(checks.issue_registry(self.root)["resolved_ids"], ["ISSUE-1"])

    def test_open_current_issue_and_unsubstantiated_resolution_are_rejected(self):
        path = "fidelity/issues/registry.json"
        self.write_json(path, {"schema_version": 1, "issues": [{"id": "ISSUE-1", "status": "open"}]})
        with self.assertRaisesRegex(EvidenceError, "Unresolved current issue"):
            checks.issue_registry(self.root)
        self.write_json(path, {"schema_version": 1, "issues": [{"id": "ISSUE-1", "status": "resolved", "evidence": []}]})
        with self.assertRaisesRegex(EvidenceError, "nonempty list"):
            checks.issue_registry(self.root)

    def test_math_may_not_import_exporter_tooling(self):
        self.write("FidelityLean/Certificates.lean", "import FidelityLean.Export\n")
        with self.assertRaisesRegex(EvidenceError, "forbidden_tool_import"):
            checks.source_audit(self.root)


class MetadataRoleTests(EvidenceFixture):
    def reverse_fixture(self):
        packet_path = "fidelity/packets/test-reverse/implementation_environment.json"
        self.write_json(packet_path, {"schema_version": 1, "original_environment_sha256": digest(self.root / self.environment_path),
                                     "decls": self.environment["decls"]})
        declaration = self.environment["decls"][0]
        record = {"name": declaration["name"], "module": declaration["module"], "kind": declaration["kind"],
            "full_type": declaration["type"], "full_type_sha256": digest_bytes(declaration["type"].encode()),
            "axioms": [], "value_available": True, "project_type_dependencies": [], "project_value_dependencies": []}
        return {"schema_version": 1, "role": "lean_reverse", "reviewer": {"id": "blind-reviewer", "independent": True},
            "inputs": {self.environment_path: digest(self.root / self.environment_path), packet_path: digest(self.root / packet_path)},
            "inspected_inputs": [{"path": packet_path, "sha256": digest(self.root / packet_path), "read": True}],
            "declarations": [record], "objects": [], "coverage": {"all_decl_ids_indexed": [declaration["name"]]},
            "module_index": {declaration["module"]: [declaration["name"]]}}

    def test_reverse_metadata_preserves_exact_export_and_does_not_provide_semantic_verdict(self):
        data = self.reverse_fixture()
        result = metadata.lean_reverse(self.root, data)
        self.assertEqual(result["declarations"], 1)
        self.assertIn("not provided", result["semantic_verdict"])
        data["declarations"][0]["full_type"] = "False"
        with self.assertRaisesRegex(EvidenceError, "type differs from export"):
            metadata.lean_reverse(self.root, data)

    def test_reverse_metadata_rejects_paper_leakage_and_incomplete_coverage(self):
        data = self.reverse_fixture()
        data["inputs"]["fidelity/inputs/authoritative.pdf"] = digest(self.root / "fidelity/inputs/authoritative.pdf")
        with self.assertRaisesRegex(EvidenceError, "implementation-only role"):
            metadata.lean_reverse(self.root, data)
        data = self.reverse_fixture()
        data["coverage"]["all_decl_ids_indexed"] = []
        with self.assertRaisesRegex(EvidenceError, "coverage inventory"):
            metadata.lean_reverse(self.root, data)

    def test_known_metadata_role_requires_separate_validation_and_is_not_semantic_vote(self):
        data = self.reverse_fixture()
        metadata.lean_reverse(self.root, data)
        self.write_json("fidelity/reviews/lean_reverse.json", data)
        self.create_reviews()
        with self.assertRaisesRegex(EvidenceError, "independent validator"):
            checks.reviews(self.root, self.inputs, self.claims, self.env, canonical_digest(self.environment["decls"]))
        result = checks.reviews(self.root, self.inputs, self.claims, self.env,
            canonical_digest(self.environment["decls"]), validated_metadata_roles={"lean_reverse"})
        self.assertEqual(len(result["semantic"]), 2)
        self.assertEqual(len(result["route"]), 1)
        data["role"] = "unknown_historical_audit"
        self.write_json("fidelity/reviews/lean_reverse.json", data)
        with self.assertRaisesRegex(EvidenceError, "Unknown review role"):
            self.validate_reviews()

    def test_reconciliation_validates_frozen_alignment_and_unique_atom_coverage(self):
        data = read_json(self.root / "fidelity/canonical_claims.json")
        claim = data["claims"][0]
        claim.update(kind="statement", page=1, locator="Theorem 1", statement="True")
        claim["declarations"] = []
        frozen = self.write_json("fidelity/specs/canonical_math.json", data)
        inputs = {}
        for side in ("a", "b"):
            self.write(f"fidelity/specs/paper_{side}.md", "independent paper extraction")
            for ext in ("json", "md"):
                name = f"fidelity/specs/paper_{side}.{ext}"
                inputs[name] = digest(self.root / name)
        for name in ("fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt"):
            inputs[name] = digest(self.root / name)
        alignment = {field: claim[field] for field in ("kind", "page", "locator", "paper_a", "paper_b", "mapping_relation", "statement", "source_evidence")}
        alignment["canonical_id"] = claim["id"]
        report = {"schema_version": 1, "role": "spec_reconciliation", "inputs": inputs,
            "independent_identity": {"task_identity": "paper-only-reconciler", "role": "source reconciliation", "method": "Independent source adjudication"},
            "open_issues": [], "canonical_alignment": [alignment], "paper_b_alignment": [{"paper_b_id": "paper_b.one", "canonical_ids": [claim["id"]]}],
            "adjudications": [], "validation": {side: {"atoms": 1, "covered_unique_atoms": 1} for side in ("paper_a", "paper_b")}}
        specs = checks.specifications(self.root)
        self.assertEqual(metadata.reconciliation(self.root, report, specs, frozen_sha256=digest(frozen))["canonical_claims"], 1)
        report["canonical_alignment"][0]["paper_a"] = []
        with self.assertRaisesRegex(EvidenceError, "differs from frozen"):
            metadata.reconciliation(self.root, report, specs, frozen_sha256=digest(frozen))


class OrchestrationTests(EvidenceFixture):
    def test_global_review_failure_preserves_verified_claim_dimensions_and_missing_evidence(self):
        self.claims["claim.unreviewed"] = {**copy.deepcopy(self.claims["claim.one"]), "id": "claim.unreviewed"}
        self.write_json("fidelity/canonical_claims.json", {"schema_version": 1, "claims": list(self.claims.values())})
        self.inputs = input_snapshot(self.root)
        self.create_reviews()
        collector = {}
        with self.assertRaisesRegex(EvidenceError, "claim coverage differs"):
            checks.reviews(self.root, self.inputs, self.claims, self.env,
                canonical_digest(self.environment["decls"]), validated_metadata_roles={"lean_reverse"}, claim_evidence=collector)
        self.assertEqual(collector["claim.one"]["objects"]["status"], "pass")
        self.assertEqual(collector["claim.unreviewed"]["objects"]["status"], "blocked")
        runner = Runner(self.root, "granular-review-run")
        runner.canonical_claims = self.claims
        runner.report["review_claim_evidence"] = collector
        for name in ("canonical_coverage", "source_stability"):
            runner.report["steps"][name] = {"status": "pass"}
        runner.report["steps"]["reviews"] = {"status": "fail"}
        self.assertNotEqual(runner.finish(), 0)
        statuses = runner.report["claim_status"]
        self.assertEqual(statuses["claim.one"]["dimensions"]["object_correspondence"], "pass")
        self.assertEqual(statuses["claim.unreviewed"]["dimensions"]["object_correspondence"], "blocked")
        self.assertTrue(statuses["claim.one"]["verified_evidence"]["objects"]["reviews"])

    def test_one_failed_dimension_does_not_erase_other_verified_dimensions(self):
        self.create_reviews()
        path = self.root / "fidelity/reviews/reviewer-one.json"
        data = read_json(path)
        data["claims"][0]["dimensions"]["hypotheses"]["evidence"] = []
        save_json(path, data)
        collector = {}
        with self.assertRaises(EvidenceError):
            checks.reviews(self.root, self.inputs, self.claims, self.env,
                canonical_digest(self.environment["decls"]), validated_metadata_roles={"lean_reverse"}, claim_evidence=collector)
        self.assertEqual(collector["claim.one"]["objects"]["status"], "pass")
        self.assertEqual(collector["claim.one"]["hypotheses"]["status"], "fail")

    def test_receiver_global_elan_home_is_preserved_without_local_toolchain(self):
        with patch.dict(os.environ, {"ELAN_HOME": "/receiver/global/elan"}):
            runner = Runner(self.root, "global-elan-run")
        self.assertEqual(runner.env["ELAN_HOME"], "/receiver/global/elan")

    def test_certificate_modules_may_be_split_without_an_empty_named_aggregate(self):
        (self.root / "FidelityLean/Certificates.lean").rename(self.root / "FidelityLean/MainCertificates.lean")
        runner = Runner(self.root, "split-certificates-run")
        modules = {path.stem for path in runner.fidelity_order(self.root)}
        self.assertIn("MainCertificates", modules)
        self.assertIn("Spec", modules)
        self.assertIn("Export", modules)
    def test_static_only_never_establishes_overall_or_reproduction_pass(self):
        runner = Runner(self.root, "static-run", static_only=True)
        self.assertNotEqual(runner.run(), 0)
        report = read_json(runner.folder / "report.json")
        self.assertNotEqual(report["overall"], "pass")
        self.assertNotEqual(report["dimensions"]["reproduction"], "pass")
        self.assertEqual(report["steps"]["baseline"]["status"], "pass")
        self.assertTrue(report["finished_at"])

    def test_skip_build_never_accepts_reproduction(self):
        runner = Runner(self.root, "skip-run", skip_build=True)
        for name in ("snapshot", "protocol", "baseline", "source_audit", "specifications", "canonical_coverage",
                     "tools", "dependencies", "build", "fidelity_compile", "environment_export",
                     "environment_validation", "reviews", "exact_experiments", "clean_rebuild",
                     "archive_rebuild", "source_stability", "issues"):
            runner.report["steps"][name] = {"status": "pass"}
        self.assertNotEqual(runner.finish(), 0)
        self.assertNotEqual(runner.report["dimensions"]["reproduction"], "pass")

    def test_mid_run_source_mutation_is_detected(self):
        runner = Runner(self.root, "mutation-run", static_only=True)
        runner.snapshot()
        self.write("AffineDualJT/Basic.lean", "theorem two : True := True.intro\n")
        self.assertIsNone(runner.step("source_stability", runner.stability))
        report = read_json(runner.folder / "report.json")
        self.assertEqual(report["steps"]["source_stability"]["status"], "fail")
        self.assertIn("Source mutation", report["steps"]["source_stability"]["reason"])

    def test_tool_mutation_is_detected_separately(self):
        runner = Runner(self.root, "tool-mutation-run", static_only=True)
        runner.snapshot()
        self.write("FidelityLean/Export.lean", "import Lean\n-- changed tool\n")
        with self.assertRaisesRegex(EvidenceError, "tools changed"):
            runner.stability()

    def test_mid_run_review_mutation_is_detected(self):
        self.create_reviews()
        runner = Runner(self.root, "review-mutation-run", static_only=True)
        runner.snapshot()
        path = self.root / "fidelity/reviews/reviewer-one.json"
        review = read_json(path)
        review["open_issues"] = ["Newly discovered discrepancy"]
        save_json(path, review)
        with self.assertRaisesRegex(EvidenceError, "Review or issue artifacts changed"):
            runner.stability()

    def test_missing_tool_leaves_recoverable_nonpassing_report(self):
        runner = Runner(self.root, "missing-tool-run")
        runner.snapshot()
        with patch("fidelity.runner.shutil.which", return_value=None):
            self.assertIsNone(runner.step("tools", runner.tools))
        report = read_json(runner.folder / "report.json")
        self.assertEqual(report["steps"]["tools"]["status"], "blocked")
        self.assertNotEqual(runner.finish(), 0)

    def test_missing_command_is_logged_with_exit_code_and_hashes(self):
        runner = Runner(self.root, "command-run")
        runner.snapshot()
        result = runner.command("missing-command", ["/absolutely/missing/fidelity-test-tool"])
        self.assertEqual(result["status"], "blocked")
        self.assertIsNone(result["exit_code"])
        self.assertEqual(result["input_snapshot_sha256"], runner.report["snapshot_sha256"])
        self.assertEqual(len(result["stderr_sha256"]), 64)
        self.assertIn("duration_seconds", result)

    def test_export_normalization_preserves_raw_and_binds_all_modules(self):
        runner = Runner(self.root, "export-run")
        runner.snapshot()
        runner.lake = "fixture-lake"
        commands = []
        def export_command(name, argv):
            commands.append(argv)
            raw = copy.deepcopy(self.environment)
            raw["decls"][0]["type_hash"] = "native-hash"
            save_json(Path(argv[5]), raw)
        with patch.object(runner, "must_command", side_effect=export_command):
            result = runner.export()
        self.assertIn("AffineDualJT.Basic", commands[0])
        self.assertIn("FidelityLean.Certificates", commands[0])
        self.assertNotIn("FidelityLean.Export", commands[0])
        raw = read_json(runner.folder / "environment.raw.json")
        normalized = read_json(runner.folder / "environment.json")
        self.assertEqual(raw["decls"][0]["type_hash"], "native-hash")
        self.assertEqual(normalized["decls"][0]["type_hash"], digest_bytes(b"True"))
        self.assertEqual(normalized["decls"][0]["native_type_hash"], "native-hash")
        self.assertEqual(normalized["snapshot_sha256"], runner.report["snapshot_sha256"])
        self.assertEqual(result["declarations_sha256"], canonical_digest(normalized["decls"]))

    def test_existing_run_directory_is_never_reused(self):
        Runner(self.root, "collision-run")
        with self.assertRaisesRegex(EvidenceError, "Refusing to reuse"):
            Runner(self.root, "collision-run")

    def test_both_reproduction_mechanisms_start_without_project_artifacts(self):
        runner = Runner(self.root, "reproduction-run")
        runner.snapshot()
        runner.lake = "fixture-lake"
        (self.root / ".lake/packages").mkdir(parents=True)
        stale = self.root / ".lake/build/lib/lean/AffineDualJT/Basic.olean"
        stale.parent.mkdir(parents=True)
        stale.write_bytes(b"old project cache that must never be copied")
        projects = []
        def math_build(project, label):
            projects.append(project)
            self.assertFalse((project / ".lake/build").exists())
            self.assertTrue((project / ".lake/packages").is_symlink())
            for path in mathematical_sources(project):
                if path.relative_to(project).parts[0] == "FidelityLean":
                    continue
                output = project / ".lake/build/lib/lean" / path.relative_to(project).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(b"new isolated mathematical artifact")
            return {"modules": 2}
        def fidelity_build(project, label):
            for path in (project / "FidelityLean").glob("*.lean"):
                output = project / ".lake/build/lib/lean" / path.relative_to(project).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(b"new isolated certificate artifact")
            return {"modules": 2}
        with patch.object(runner, "build_math", side_effect=math_build), patch.object(
                runner, "compile_fidelity", side_effect=fidelity_build):
            clean = runner.reproduce("clean")
            archive = runner.reproduce("archive", from_archive=True)
        self.assertNotEqual(projects[0], projects[1])
        self.assertEqual(clean["mechanism"], "fresh-source-copy")
        self.assertEqual(archive["mechanism"], "zip-extract")
        self.assertEqual(clean["source_archive_sha256"], archive["source_archive_sha256"])
        self.assertEqual(len(clean["artifacts"]), 4)


if __name__ == "__main__":
    unittest.main()
