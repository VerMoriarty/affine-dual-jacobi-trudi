"""Repackaging must preserve the evidence closure, not only Lean sources."""
import json
import sys
from pathlib import Path
import tempfile
import zipfile

from test_fidelity import EvidenceFixture
from fidelity import checks, metadata
from fidelity.archive import inventory, completed_run_files
from fidelity.common import (EvidenceError, canonical_digest, digest, input_snapshot,
                             read_json, save_json, tool_snapshot)


class ArchiveTests(EvidenceFixture):
    def test_extracted_inventory_revalidates_blind_metadata_and_all_reviews(self):
        self.create_reviews()
        files = inventory(self.root)
        self.assertIn(self.environment_path, files)
        self.assertIn('tests/test_portability.py', files)
        self.assertTrue(any('/packets/' in name for name in files))
        with tempfile.TemporaryDirectory() as folder:
            archive = Path(folder) / 'source.zip'
            target = Path(folder) / 'extracted'
            with zipfile.ZipFile(archive, 'w') as z:
                for name in files:
                    z.write(self.root / name, name)
            with zipfile.ZipFile(archive) as z:
                z.extractall(target)
            self.assertEqual(input_snapshot(target), input_snapshot(self.root))
            metadata.lean_reverse(target, read_json(target / 'fidelity/reviews/lean_reverse.json'))
            result = checks.reviews(target, input_snapshot(target), self.claims, self.env,
                                    canonical_digest(self.environment['decls']),
                                    validated_metadata_roles={'lean_reverse'})
            self.assertEqual(len(result['semantic']), 2)
            self.assertEqual(len(result['route']), 1)

    def test_missing_or_stale_review_dependency_rejects_package(self):
        self.create_reviews()
        self.write(self.environment_path, '{"decls":[]}')
        with self.assertRaisesRegex(EvidenceError, 'Stale archive evidence'):
            inventory(self.root)
        (self.root / self.environment_path).unlink()
        with self.assertRaisesRegex(EvidenceError, 'Missing regular project file'):
            inventory(self.root)

    def test_unreferenced_large_exports_and_recursive_zips_are_excluded(self):
        self.create_reviews()
        self.write('fidelity/runs/old/environment.raw.json', '{}')
        self.write('fidelity/runs/old/reproduction-source.zip', 'unused')
        self.write('fidelity/packets/unread/manifest.json', '{}')
        files = inventory(self.root)
        self.assertNotIn('fidelity/runs/old/environment.raw.json', files)
        self.assertNotIn('fidelity/runs/old/reproduction-source.zip', files)
        self.assertNotIn('fidelity/packets/unread/manifest.json', files)

    def test_frozen_original_project_absolute_identity_relocates_with_exact_hash(self):
        name = 'FidelityLean/Spec.lean'
        self.write_json('fidelity/specs/addendum.json', {'inputs': [{
            'path': '/former/machine/affine_dual_jt_complete/' + name,
            'sha256': digest(self.root / name)}]})
        self.assertIn(name, inventory(self.root))
        self.write(name, 'changed specification')
        with self.assertRaisesRegex(EvidenceError, 'Stale archive evidence'):
            inventory(self.root)

    def completed_fixture(self):
        run = 'completed'
        prefix = 'fidelity/runs/' + run
        output = self.write(prefix + '/000-command.stdout.log', 'actual command output')
        error = self.write(prefix + '/000-command.stderr.log', '')
        inputs = input_snapshot(self.root)
        self.write_json(prefix + '/inputs.json', {'inputs': inputs, 'snapshot_sha256': canonical_digest(inputs)})
        report = {'run_id': run, 'overall': 'blocked', 'finished_at': '2026-10-31T00:00:00Z',
                  'inputs': inputs, 'tools': tool_snapshot(self.root), 'steps': {},
                  'review_and_issue_inputs': {p.relative_to(self.root).as_posix(): digest(p)
                    for folder in ('fidelity/reviews', 'fidelity/issues')
                    for p in (self.root / folder).rglob('*.json')},
                  'commands': [{'finished_at': '2026-10-31T00:00:00Z', 'status': 'pass', 'exit_code': 0,
                                'stdout': output.relative_to(self.root).as_posix(), 'stdout_sha256': digest(output),
                                'stderr': error.relative_to(self.root).as_posix(), 'stderr_sha256': digest(error)}]}
        self.write_json(prefix + '/report.json', report)
        return prefix, report

    def test_completed_bundle_checks_real_logs_and_refuses_stale_command_output(self):
        prefix, _ = self.completed_fixture()
        files, receipt = completed_run_files(self.root, 'completed')
        self.assertIn(prefix + '/000-command.stdout.log', files)
        self.assertEqual(receipt['overall'], 'blocked')
        self.write(prefix + '/000-command.stdout.log', 'overwritten log')
        with self.assertRaisesRegex(EvidenceError, 'artifact hash differs'):
            completed_run_files(self.root, 'completed')

    def test_unfinished_or_stale_or_fake_pass_run_is_never_packaged_as_accepted(self):
        prefix, report = self.completed_fixture()
        report['finished_at'] = None
        self.write_json(prefix + '/report.json', report)
        with self.assertRaisesRegex(EvidenceError, 'not completed'):
            completed_run_files(self.root, 'completed')
        report['finished_at'] = 'done'
        report['overall'] = 'pass'
        self.write_json(prefix + '/report.json', report)
        with self.assertRaisesRegex(EvidenceError, 'pass label'):
            completed_run_files(self.root, 'completed')
        report['overall'] = 'blocked'
        self.write_json(prefix + '/report.json', report)
        self.write('AffineDualJT/Basic.lean', 'changed source')
        with self.assertRaisesRegex(EvidenceError, 'stale for current'):
            completed_run_files(self.root, 'completed')


class ExactDetectorEvidenceTests(EvidenceFixture):
    def detector_output(self):
        self.write_json('fidelity/experiments.json', {'schema_version': 1, 'required_cases': ['mutation-test']})
        return {'schema_version': 1, 'arithmetic': 'exact', 'open_issues': [], 'cases': [{
            'id': 'mutation-test', 'claims': ['claim.one'], 'status': 'pass',
            'comparisons': [{'left': '1', 'right': '1'}],
            'details': {'expected_counterexample': True, 'evidence_role': 'supporting_only',
                        'correct': '5/2', 'mutant': '5', 'difference': '5/2',
                        'independent_detector_value': '5/2', 'independent_detector_path': 'independent Weyl sum'}}]}

    def test_equal_mutant_is_rejected_even_when_pass_and_detection_flag_are_true(self):
        data = self.detector_output()
        self.assertEqual(checks.experiments(self.root, data, self.claims)['independently_detected_mutations'], 1)
        data['cases'][0]['details']['mutant'] = '5/2'
        data['cases'][0]['details']['difference'] = '0'
        with self.assertRaisesRegex(EvidenceError, 'Contradictory exact mutation'):
            checks.experiments(self.root, data, self.claims)

    def test_forged_difference_or_independent_reference_is_rejected(self):
        data = self.detector_output()
        data['cases'][0]['details']['difference'] = '3'
        with self.assertRaisesRegex(EvidenceError, 'Contradictory exact mutation'):
            checks.experiments(self.root, data, self.claims)
        data = self.detector_output()
        data['cases'][0]['details']['independent_detector_value'] = '7/2'
        with self.assertRaisesRegex(EvidenceError, 'Contradictory exact mutation'):
            checks.experiments(self.root, data, self.claims)


class CleanBuildBoundaryTests(EvidenceFixture):
    def test_old_project_artifacts_are_removed_and_dependency_cache_is_preserved(self):
        from unittest.mock import patch
        from fidelity.runner import Runner
        stale = self.write('.lake/build/lib/lean/AffineDualJT/Basic.olean', 'submitted artifact')
        dependency = self.write('.lake/packages/mathlib/cache-marker', 'locked dependency cache')
        runner = Runner(self.root, 'fresh-build-fixture')
        runner.lake = '/fixed/lake'
        with patch.object(runner, 'must_command', return_value={'exit_code': 0}) as command:
            result = runner.build_math(self.root, 'fresh')
        self.assertFalse(stale.exists())
        self.assertTrue(dependency.exists())
        self.assertTrue(result['project_artifacts_cleared_before_build'])
        self.assertIn('+AffineDualJT.Basic', command.call_args.args[1])

    def test_build_directory_symlink_is_rejected_without_deleting_its_target(self):
        from fidelity.runner import Runner
        outside = self.root / 'unrelated'
        outside.mkdir()
        marker = self.write('unrelated/keep', 'preserve this')
        (self.root / '.lake').mkdir()
        (self.root / '.lake/build').symlink_to(outside, target_is_directory=True)
        runner = Runner(self.root, 'symlink-build-fixture')
        runner.lake = '/fixed/lake'
        with self.assertRaisesRegex(EvidenceError, 'must not be a symlink'):
            runner.build_math(self.root, 'fresh')
        self.assertTrue(marker.exists())


class HashCacheStabilityTests(EvidenceFixture):
    def test_mutation_after_evidence_collection_invalidates_all_dependent_review_judgments(self):
        from unittest.mock import patch
        self.create_reviews()
        original = checks._judgment
        calls = 0
        def mutate_after_last_judgment(root, judgment, label, hashes=None):
            nonlocal calls
            result = original(root, judgment, label, hashes)
            calls += 1
            if calls == 11:
                self.write('fidelity/specs/paper_a.json', 'changed after cached verification')
            return result
        collector = {}
        with patch.object(checks, '_judgment', side_effect=mutate_after_last_judgment):
            with self.assertRaisesRegex(EvidenceError, 'Evidence changed during review validation'):
                checks.reviews(self.root, self.inputs, self.claims, self.env,
                               canonical_digest(self.environment['decls']),
                               validated_metadata_roles={'lean_reverse'}, claim_evidence=collector)
        self.assertEqual(collector['claim.one']['objects']['status'], 'fail')

    def test_archive_rehashes_cached_evidence_before_finishing(self):
        from unittest.mock import patch
        from fidelity import archive
        self.create_reviews()
        original = archive.portable_paths
        def mutate_after_collection(names):
            original(names)
            self.write(self.environment_path, 'changed after evidence closure')
        with patch.object(archive, 'portable_paths', side_effect=mutate_after_collection):
            with self.assertRaisesRegex(EvidenceError, 'Archive evidence changed during closure'):
                archive.inventory(self.root)


class CompletedBundleRegressionTests(EvidenceFixture):
    completed_fixture = ArchiveTests.completed_fixture

    def test_new_review_or_issue_invalidates_completed_run(self):
        self.completed_fixture()
        self.write_json('fidelity/issues/new-finding.json', {'id': 'unreviewed', 'status': 'open'})
        with self.assertRaisesRegex(EvidenceError, 'stale review or issue evidence'):
            completed_run_files(self.root, 'completed')

    def test_reproduction_inventory_must_match_the_actual_verified_archive(self):
        from fidelity.common import digest_bytes
        prefix, report = self.completed_fixture()
        archive = self.root / prefix / 'reproduction-clean-source.zip'
        with zipfile.ZipFile(archive, 'w') as z:
            z.writestr('input.lean', 'actual source')
        manifest_name = prefix + '/reproduction-clean-manifest.json'
        manifest = self.write_json(manifest_name, {'input.lean': digest_bytes(b'actual source')})
        report['steps']['clean_rebuild'] = {'status': 'pass', 'details': {
            'source_archive_sha256': digest(archive),
            'source_manifest': {'path': manifest_name, 'sha256': digest(manifest)}}}
        self.write_json(prefix + '/report.json', report)
        files, receipt = completed_run_files(self.root, 'completed')
        self.assertIn(manifest_name, files)
        self.assertNotIn(archive.relative_to(self.root).as_posix(), files)
        self.write_json(manifest_name, {'forged.lean': '0' * 64})
        with self.assertRaisesRegex(EvidenceError, 'artifact hash differs'):
            completed_run_files(self.root, 'completed')
        report['steps']['clean_rebuild']['details']['source_manifest']['sha256'] = digest(manifest)
        self.write_json(prefix + '/report.json', report)
        with self.assertRaisesRegex(EvidenceError, 'inventory differs from the verified ZIP'):
            completed_run_files(self.root, 'completed')

    def test_failed_command_keeps_its_generated_counterexample_json(self):
        from fidelity.runner import Runner
        runner = Runner(self.root, 'failed-diagnostic')
        runner.snapshot()
        target = runner.folder / 'experiments.json'
        code = 'from pathlib import Path; Path(' + repr(str(target)) + ').write_text(\'{"counterexample": true}\'); raise SystemExit(2)'
        command = runner.command('exact-experiments', [sys.executable, '-c', code])
        self.assertEqual(command['exit_code'], 2)
        runner.finish()
        files, receipt = completed_run_files(self.root, 'failed-diagnostic')
        self.assertIn(target.relative_to(runner.root).as_posix(), files)
        self.assertNotEqual(receipt['overall'], 'pass')


class ProtocolSchemaPackagingTests(EvidenceFixture):
    def test_protocol_examples_are_delivered_without_being_followed_as_evidence(self):
        protocol = read_json(self.root / 'fidelity/protocol.json')
        protocol['example'] = {'path': 'absolute or project-relative source path',
                               'sha256': '64 lowercase hexadecimal characters'}
        self.write_json('fidelity/protocol.json', protocol)
        self.create_reviews()
        selected = inventory(self.root)
        self.assertIn('fidelity/protocol.json', selected)
        self.assertNotIn('absolute or project-relative source path', selected)
