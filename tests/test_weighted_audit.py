#!/usr/bin/env python3
"""Tests for the T-004 weighted branch-mismatch analyser.

Three concerns are kept in separate classes, because conflating them is how
the T-003 checker went wrong:

* `FileIntegrityTests`   -- parsing, arity, finiteness, coverage, duplicates.
* `AlgebraicConsistencyTests` -- weighted sums, signs, cancellation, zero
  weights, multiplicity, group separation, hand-checkable totals.
* `GroupingTests`        -- the accumulator key and outer-identity contract.
* `SavedEvidenceTests`   -- the committed 3702-record evidence, with no
  BerkeleyGW rebuild or rerun.
* `PhysicalValidityLabelTests` -- that the output refuses to call itself a
  self-energy and enumerates every missing factor.

The synthetic fixture is built so its answer is exact and hand-checkable:
with `w = 8`, `x = 8.25`, `ieps = 0.5`, `occ = 0.5`,

    Omega2      = 8^2 * 0.5            = 32
    den_merged  = 2*8*(8.25+8)         = 260
    den_generic = (8.25-8)*(8.25+8)    = 4.0625
    mismatch    = 0.5*(32/260 + 32/4.0625)
                = 0.5*(8/65 + 512/65) = 0.5*8 = 4     exactly

so a record with weight `K = aqsn*aqsm*vcoul` contributes exactly `4*K`.
"""

from fractions import Fraction as F
import contextlib
import functools
import io
import json
import pathlib
import re
import shutil
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "weighted_audit"))
sys.path.insert(0, str(ROOT / "bgw" / "occupation_audit"))

import check_occupation as co        # noqa: E402
import weighted_mismatch as wm       # noqa: E402

FIXTURES = ROOT / "bgw" / "weighted_audit" / "fixtures"
RECORDS = FIXTURES / "t004_nearpole_weighted.dat"
ACCUMULATORS = FIXTURES / "t004_accumulators.dat"
PROBE = FIXTURES / "fermi_branch_occ_counts.dat"
CONTROL = FIXTURES / "control_branch_occ_counts.dat"

#: exact mismatch of the synthetic record, see the module docstring
SYNTH_MISMATCH = F(4)


def run_main(argv):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = wm.main(argv)
    return rc, json.loads(buf.getvalue())


@functools.lru_cache(maxsize=1)
def saved_evidence():
    """Analyse the committed 3702-record evidence once per process.

    Without the cache each saved-evidence assertion re-ran the whole analysis
    and the file took ~22 s, which is too slow for routine gate runs.
    """
    return run_main([str(RECORDS), "--accumulators", str(ACCUMULATORS)])


def synth_record(rec=1, call_id=1, iw=2, aqsn=1.0, aqsm=1.0, vcoul=0.25,
                 band_in=8, **over):
    """A self-consistent near-pole occ=0.5 record with mismatch exactly 4."""
    w, x, ieps, occ = 8.0, 8.25, 0.5, 0.5
    e_n1kq = -2.0
    e_lk = x - (iw - 2) * co.SIG_DW + e_n1kq
    w2 = w * w
    omega2 = w2 * ieps
    delw = w / (x - w)
    den_np = 4 * w2 * (delw + 0.5)
    ssx = -omega2 * delw / den_np
    f = dict(
        rec=rec, call_id=call_id, n1true=1, n1=1, iw=iw, igp=2, ig=4, branch=2,
        band_in=band_in, il=band_in, iband=band_in, ispin=1, icalc=1,
        occ=occ, vcoul=vcoul, ieps=ieps, wtilde_re=w, wtilde_im=0.0,
        wtilde2=w2, wxt=x, omega2=omega2, delw=delw, delwr=delw * delw,
        wdiffr=(x - w) ** 2, limittwo=co.LIMITTWO, limitone=co.LIMITONE,
        ssx_pre=ssx, ssx_post=ssx, sch=0.0,
        den_generic=x * x - w2, den_nearpole=den_np, den_merged=2 * w * (x + w),
        e_lk=e_lk, e_n1kq=e_n1kq, efermi=e_n1kq, occ_broadening=0.1,
        aqsn=aqsn, aqsm=aqsm, qk1=0.0, qk2=0.0, qk3=0.5,
    )
    f.update(over)
    ints = " ".join(str(f[k]) for k in wm.INT_FIELDS)
    reals = " ".join(f"{f[k]:.17E}" for k in wm.REAL_FIELDS)
    return ints + " " + reals


def synth_acc(call_id=1, iw=2, asx=-1.0, ach=0.0, band_in=8, subtotal=None):
    """A synthetic accumulator row.

    `subtotal` is the Fortran's own sum of `K*L` over the exported records of
    this group. It defaults to the value the synthetic record actually implies
    (`K*L` with `K = 1*1*0.25`), so the reconstruction check passes; tests that
    want to break it pass an explicit value.
    """
    if subtotal is None:
        w, x, ieps, occ = 8.0, 8.25, 0.5, 0.5
        delw = w / (x - w)
        ssx = -(w * w * ieps) * delw / (4 * w * w * (delw + 0.5))
        subtotal = 0.25 * (-occ * ssx)
    f = dict(call_id=call_id, band_in=band_in, il=band_in, ispin=1, icalc=1,
             iw=iw, nend=3, asxtemp=asx, achtemp=ach,
             qk1=0.0, qk2=0.0, qk3=0.5, subtotal_in_code=subtotal)
    ints = " ".join(str(f[k]) for k in wm.ACC_INT_FIELDS)
    reals = " ".join(f"{f[k]:.17E}" for k in wm.ACC_REAL_FIELDS)
    return ints + " " + reals


class TempCase(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp(prefix="t004-"))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    @staticmethod
    def _subtotals(records):
        """K*L per (call_id, iw), exactly as the Fortran would accumulate it."""
        out = {}
        for line in records:
            r = wm.parse(line + "\n")[0]
            K = F(r["aqsn"]) * F(r["aqsm"]) * F(r["vcoul"])
            L = -F(r["occ"]) * F(r["ssx_post"]) + F(r["sch"]) / 2
            key = (r["call_id"], r["iw"])
            out[key] = out.get(key, F(0)) + K * L
        return out

    def build(self, records, accs=None, expect=None, acc_kwargs=None):
        """Write a synthetic dataset and run the analyser over it.

        When `accs` is not given, one accumulator row per group is generated
        with `subtotal_in_code` equal to the group's true sum of `K*L`, so the
        reconstruction check passes. `acc_kwargs` overrides per-group fields.
        """
        rp = self.tmp / "records.dat"
        rp.write_text("\n".join(records) + "\n")
        if accs is None:
            subs = self._subtotals(records)
            accs = [synth_acc(call_id=c, iw=i, subtotal=float(v),
                              **(acc_kwargs or {}).get((c, i), {}))
                    for (c, i), v in subs.items()]
        ap = self.tmp / "acc.dat"
        ap.write_text("\n".join(accs) + "\n")
        return run_main([str(rp), "--accumulators", str(ap), "--no-tally",
                         "--expect-records",
                         str(expect if expect is not None else len(records))])


# ------------------------------------------------------------ file integrity

class FileIntegrityTests(TempCase):
    def test_empty_records_rejected(self):
        for text in ("", "\n\n", "# comment only\n"):
            with self.assertRaises(wm.WeightedError):
                wm.parse(text)

    def test_wrong_arity_rejected(self):
        short = " ".join(synth_record().split()[:30])
        with self.assertRaises(wm.WeightedError) as cm:
            wm.parse(short + "\n")
        self.assertIn("format reversion", str(cm.exception))

    def test_nonfinite_rejected(self):
        toks = synth_record().split()
        toks[len(wm.INT_FIELDS) + wm.REAL_FIELDS.index("aqsn")] = "NaN"
        with self.assertRaises(wm.WeightedError) as cm:
            wm.parse(" ".join(toks) + "\n")
        self.assertIn("not finite", str(cm.exception))

    def test_dropped_record_rejected_by_coverage(self):
        recs = [synth_record(rec=i) for i in range(1, 4)]
        with self.assertRaises(wm.WeightedError) as cm:
            self.build(recs[:2], expect=3)
        self.assertIn("expected exactly 3", str(cm.exception))

    def test_duplicate_record_id_rejected(self):
        recs = [synth_record(rec=1), synth_record(rec=1)]
        with self.assertRaises(wm.WeightedError) as cm:
            self.build(recs)
        self.assertIn("duplicate record ids", str(cm.exception))

    def test_noncontiguous_ids_rejected(self):
        recs = [synth_record(rec=1), synth_record(rec=7)]
        with self.assertRaises(wm.WeightedError) as cm:
            self.build(recs)
        self.assertIn("exactly 1..2", str(cm.exception))

    def test_duplicate_accumulator_key_rejected(self):
        with self.assertRaises(wm.WeightedError) as cm:
            self.build([synth_record()],
                       accs=[synth_acc(), synth_acc()])
        self.assertIn("duplicate key", str(cm.exception))

    def test_accumulator_wrong_arity_rejected(self):
        with self.assertRaises(wm.WeightedError) as cm:
            self.build([synth_record()],
                       accs=[" ".join(synth_acc().split()[:8])])
        self.assertIn("accumulator line", str(cm.exception))

    def test_nonreal_pole_rejected_explicitly(self):
        """Real flavor: no conjugation is applied, so a complex pole is refused."""
        with self.assertRaises(wm.WeightedError) as cm:
            self.build([synth_record(wtilde_im=1.0)])
        self.assertIn("imaginary", str(cm.exception))
        self.assertIn("not approximated", str(cm.exception))


# ------------------------------------------------------ algebraic consistency

class AlgebraicConsistencyTests(TempCase):
    def test_single_record_hand_checkable_total(self):
        """weight K = 1*1*0.25 = 0.25, mismatch 4, so K*m = 1 exactly."""
        rc, out = self.build([synth_record()])
        self.assertEqual(rc, 0)
        self.assertEqual(out["events_summed"], 1)
        self.assertAlmostEqual(out["total_signed_weighted_mismatch"], 1.0,
                               places=12)
        self.assertAlmostEqual(out["total_sum_abs_weighted_mismatch"], 1.0,
                               places=12)

    def test_exact_cancellation_keeps_absolute_sum(self):
        recs = [synth_record(rec=1, aqsn=1.0),
                synth_record(rec=2, aqsn=-1.0)]
        rc, out = self.build(recs)
        self.assertAlmostEqual(out["total_signed_weighted_mismatch"], 0.0,
                               places=12)
        self.assertAlmostEqual(out["total_sum_abs_weighted_mismatch"], 2.0,
                               places=12)
        self.assertEqual(out["total_cancellation_ratio_signed_over_abs"], 0.0)

    def test_signed_weight_from_each_matrix_element(self):
        for aqsn, aqsm, want in ((1.0, 1.0, 1.0), (-1.0, 1.0, -1.0),
                                 (1.0, -1.0, -1.0), (-1.0, -1.0, 1.0)):
            with self.subTest(aqsn=aqsn, aqsm=aqsm):
                _, out = self.build([synth_record(aqsn=aqsn, aqsm=aqsm)])
                self.assertAlmostEqual(
                    out["total_signed_weighted_mismatch"], want, places=12)

    def test_zero_weight_contributes_nothing(self):
        for kw in (dict(vcoul=0.0), dict(aqsn=0.0), dict(aqsm=0.0)):
            with self.subTest(**kw):
                _, out = self.build([synth_record(**kw)])
                self.assertEqual(out["total_signed_weighted_mismatch"], 0.0)
                self.assertEqual(out["total_sum_abs_weighted_mismatch"], 0.0)
                self.assertEqual(out["events_summed"], 1)

    def test_multiplicity_is_retained(self):
        """Identical-valued records at distinct ids must all be counted."""
        recs = [synth_record(rec=i) for i in range(1, 6)]
        _, out = self.build(recs)
        self.assertEqual(out["events_summed"], 5)
        self.assertAlmostEqual(out["total_signed_weighted_mismatch"], 5.0,
                               places=12)

    def test_largest_term_is_identified(self):
        recs = [synth_record(rec=1, vcoul=0.25),
                synth_record(rec=2, vcoul=0.75)]
        _, out = self.build(recs)
        self.assertAlmostEqual(out["largest_abs_term"], 3.0, places=12)
        self.assertEqual(out["largest_abs_term_record"], 2)

    def test_inconsistent_derived_quantity_rejected(self):
        """Reuses the T-003 checker's residual gate, unmodified."""
        with self.assertRaises(co.RecordError) as cm:
            self.build([synth_record(omega2=999999.0)])
        self.assertIn("omega2", str(cm.exception))

    def test_subtotal_disagreement_is_caught_and_correctly_scoped(self):
        """The in-code subtotal must gate the Python subtotal, and the message
        must not overdiagnose which term is at fault.

        The former message said "the weight or local value reconstruction is
        wrong", which names a per-term cause the check cannot actually
        localise: per-term errors can cancel inside a subtotal.
        """
        with self.assertRaises(wm.WeightedError) as cm:
            self.build([synth_record()],
                       accs=[synth_acc(subtotal=123.456)])
        message = str(cm.exception)
        self.assertIn("SUBTOTAL", message)
        self.assertIn("does not by itself identify", message)
        self.assertNotIn("reconstruction is wrong", message)

    def test_subtotal_within_float_summation_noise_is_accepted(self):
        subs = self._subtotals([synth_record()])
        true = float(subs[(1, 2)])
        _, out = self.build([synth_record()],
                            accs=[synth_acc(subtotal=true * (1 + 1e-14))])
        self.assertEqual(out["events_summed"], 1)

    def test_every_record_is_accounted_for(self):
        recs = [synth_record(rec=i) for i in range(1, 4)]
        _, out = self.build(recs)
        self.assertEqual(out["events_accounted"], 3)
        self.assertEqual(out["singular_records_excluded"], [])


# --------------------------------------------------------------- grouping

class GroupingTests(TempCase):
    def test_different_iw_are_separate_groups(self):
        """Summing across iw would add different energy evaluations."""
        recs = [synth_record(rec=1, iw=2), synth_record(rec=2, iw=3)]
        _, out = self.build(recs)
        self.assertEqual(out["groups"], 2)
        self.assertEqual({g["iw"] for g in out["group_detail"]}, {2, 3})

    def test_different_calls_are_separate_groups(self):
        recs = [synth_record(rec=1, call_id=1), synth_record(rec=2, call_id=2)]
        _, out = self.build(recs)
        self.assertEqual(out["groups"], 2)

    def test_same_call_and_iw_merge(self):
        recs = [synth_record(rec=1, call_id=3), synth_record(rec=2, call_id=3)]
        _, out = self.build(recs)
        self.assertEqual(out["groups"], 1)
        self.assertEqual(out["group_detail"][0]["events"], 2)

    def test_inconsistent_outer_identity_in_one_call_rejected(self):
        """Wrong group assignment must not pass silently."""
        recs = [synth_record(rec=1, call_id=5, band_in=8),
                synth_record(rec=2, call_id=5, band_in=7)]
        with self.assertRaises(wm.WeightedError) as cm:
            self.build(recs)
        self.assertIn("two different", str(cm.exception))

    def test_missing_accumulator_is_reported_not_hidden(self):
        _, out = self.build([synth_record(call_id=9)],
                            accs=[synth_acc(call_id=42, subtotal=0.0)])
        self.assertEqual(out["groups_without_accumulator"], 1)
        g = out["group_detail"][0]
        self.assertIsNone(g["accumulator_total"])
        self.assertIn("no accumulator row", g["accumulator_note"])

    def test_accumulator_ratio_uses_asx_plus_ach(self):
        subs = self._subtotals([synth_record()])
        _, out = self.build([synth_record()],
                            accs=[synth_acc(asx=-3.0, ach=1.0,
                                            subtotal=float(subs[(1, 2)]))])
        g = out["group_detail"][0]
        self.assertAlmostEqual(g["accumulator_total"], -2.0, places=12)
        self.assertAlmostEqual(g["signed_over_accumulator"], 0.5, places=12)

    def test_small_reference_accumulator_is_flagged(self):
        """A ratio against a near-zero reference is not evidence of an effect."""
        recs = [synth_record(rec=1, call_id=1), synth_record(rec=2, call_id=2)]
        subs = self._subtotals(recs)
        accs = [synth_acc(call_id=1, asx=-100.0,
                          subtotal=float(subs[(1, 2)])),     # big reference
                synth_acc(call_id=2, asx=-1e-9,
                          subtotal=float(subs[(2, 2)]))]     # tiny reference
        _, out = self.build(recs, accs=accs)
        flagged = {g["call_id"]: g["accumulator_is_small_reference"]
                   for g in out["group_detail"]}
        self.assertFalse(flagged[1])
        self.assertTrue(flagged[2])
        self.assertEqual(out["groups_flagged_small_reference"], 1)
        tiny = next(g for g in out["group_detail"] if g["call_id"] == 2)
        self.assertIn("small-reference artefact", tiny["accumulator_note"])

    def test_max_ratio_is_reported_both_with_and_without_small_references(self):
        recs = [synth_record(rec=1, call_id=1), synth_record(rec=2, call_id=2)]
        subs = self._subtotals(recs)
        accs = [synth_acc(call_id=1, asx=-100.0, subtotal=float(subs[(1, 2)])),
                synth_acc(call_id=2, asx=-1e-9, subtotal=float(subs[(2, 2)]))]
        _, out = self.build(recs, accs=accs)
        self.assertGreater(out["max_group_ratio_any"], 1e6)
        self.assertAlmostEqual(
            out["max_group_ratio_excluding_small_reference"], 0.01, places=12)

    def test_accumulator_identity_must_match_its_records(self):
        """Audit finding 5: a band-999 accumulator used to pass silently."""
        subs = self._subtotals([synth_record(band_in=8)])
        with self.assertRaises(wm.WeightedError) as cm:
            self.build([synth_record(band_in=8)],
                       accs=[synth_acc(band_in=999,
                                       subtotal=float(subs[(1, 2)]))])
        self.assertIn("different outputs", str(cm.exception))

    def test_max_groups_does_not_change_global_statistics(self):
        """Smaller finding: truncation is a display option, not a filter."""
        recs = [synth_record(rec=1, call_id=1), synth_record(rec=2, call_id=2)]
        subs = self._subtotals(recs)
        accs = [synth_acc(call_id=1, asx=-100.0, subtotal=float(subs[(1, 2)])),
                synth_acc(call_id=2, asx=-1e-9, subtotal=float(subs[(2, 2)]))]
        rp = self.tmp / "r.dat"; rp.write_text("\n".join(recs) + "\n")
        ap = self.tmp / "a.dat"; ap.write_text("\n".join(accs) + "\n")
        base = run_main([str(rp), "--accumulators", str(ap), "--no-tally",
                         "--expect-records", "2"])[1]
        trunc = run_main([str(rp), "--accumulators", str(ap), "--no-tally",
                          "--expect-records", "2", "--max-groups", "1"])[1]
        self.assertEqual(len(trunc["group_detail"]), 1)
        for k in ("groups", "groups_flagged_small_reference",
                  "max_group_ratio_any",
                  "max_group_ratio_excluding_small_reference",
                  "groups_above_10pct_of_accumulator",
                  "per_call_group_l1_over_accumulators"):
            self.assertEqual(base[k], trunc[k], k)

    def test_zero_accumulator_reference_is_flagged_not_divided(self):
        subs = self._subtotals([synth_record()])
        _, out = self.build([synth_record()],
                            accs=[synth_acc(asx=0.0, ach=0.0,
                                            subtotal=float(subs[(1, 2)]))])
        g = out["group_detail"][0]
        self.assertIsNone(g["signed_over_accumulator"])
        self.assertIn("zero", g["accumulator_note"])


# ---------------------------------------------------------- saved evidence

class SavedEvidenceTests(unittest.TestCase):
    """Validates the committed evidence. No rebuild, no BerkeleyGW run."""

    def test_saved_evidence_passes(self):
        rc, out = saved_evidence()
        self.assertEqual(rc, 0)
        self.assertEqual(out["coverage"]["records"], 3702)
        self.assertTrue(out["coverage"]["ids_complete"])

    def test_export_is_tied_to_the_runs_own_tally(self):
        """The 3702 is read from the run's tally, not hard-coded."""
        _, out = saved_evidence()
        self.assertTrue(out["coverage"]["tied_to_tally"])
        self.assertEqual(out["coverage"]["counted_qualifying_events"], 3702)
        d = out["exported_records_vs_counted_events"]
        self.assertEqual(d["exported_records"], d["counted_qualifying_events"])
        self.assertTrue(d["cardinality_matches_tally"])

    def test_completeness_is_not_claimed_from_cardinality_alone(self):
        """T-004-R3 item 4: say what the check proves and what it does not."""
        _, out = saved_evidence()
        rel = out["exported_records_vs_counted_events"]["relationship"]
        self.assertIn("Cardinality and id-sequentiality", rel)
        self.assertIn("does not check", rel)
        self.assertIn("completeness_evidence", rel)
        self.assertIn("completeness_evidence", out)

    def test_tally_and_export_cannot_drift_apart(self):
        """A tally altered while preserving its row sums is still rejected."""
        import tempfile, shutil
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="t004-tie-"))
        try:
            bad = tmp / "tally.dat"
            bad.write_text(PROBE.read_text().replace(
                "branch2          76461           3702",
                "branch2          76462           3701"))
            with self.assertRaises(wm.WeightedError) as cm:
                run_main([str(RECORDS), "--accumulators", str(ACCUMULATORS),
                          "--counts", str(bad),
                          "--control-counts", str(CONTROL)])
            self.assertIn("expected exactly 3701", str(cm.exception))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    def test_no_tally_mode_says_so(self):
        _, out = run_main([str(RECORDS), "--accumulators", str(ACCUMULATORS),
                           "--no-tally", "--expect-records", "3702"])
        self.assertFalse(out["coverage"]["tied_to_tally"])
        self.assertIn("NOT tied",
                      out["exported_records_vs_counted_events"]["relationship"])
        # and it must make NO positive tally-based completeness claim
        ce = out["completeness_evidence"]
        self.assertIsNone(ce["checked here"])
        self.assertIn("--no-tally was used", ce["reason"])
        self.assertNotIn("not checked here (1) shared predicate", ce)
        for v in ce.values():
            if v:
                self.assertNotIn("cardinality equals the validated tally", v)

    def test_no_tally_coverage_failure_names_a_synthetic_contract(self):
        with self.assertRaises(wm.WeightedError) as cm:
            run_main([str(RECORDS), "--accumulators", str(ACCUMULATORS),
                      "--no-tally", "--expect-records", "5"])
        msg = str(cm.exception)
        self.assertIn("synthetic contract", msg)
        self.assertNotIn("all qualifying events", msg)

    def test_all_3702_events_accounted(self):
        _, out = saved_evidence()
        self.assertEqual(out["events_summed"], 3702)
        self.assertEqual(out["events_accounted"], 3702)
        self.assertEqual(out["singular_records_excluded"], [])
        self.assertEqual(out["groups_without_accumulator"], 0)

    def test_saved_artifact_matches_a_fresh_analyser_run(self):
        """artifacts/t004/weighted_mismatch.json must be regenerable.

        A saved artifact that has drifted from what the analyser now produces
        is worse than no artifact, because it is quoted in the review packet.
        """
        saved = json.loads(
            (ROOT / "artifacts" / "t004" / "weighted_mismatch.json").read_text())
        _, fresh = saved_evidence()
        self.assertEqual(set(saved), set(fresh),
                         "saved artifact has different keys from a fresh run")
        for k in sorted(set(saved)):
            with self.subTest(key=k):
                self.assertEqual(saved[k], fresh[k])

    def test_headline_numbers_are_stable(self):
        _, out = saved_evidence()
        self.assertAlmostEqual(out["total_signed_weighted_mismatch"],
                               0.02011641142896453, places=15)
        self.assertAlmostEqual(out["total_sum_abs_weighted_mismatch"],
                               0.0442668976572322, places=15)
        self.assertAlmostEqual(
            out["per_call_group_l1_over_accumulators"],
            0.010558548317668193, places=15)
        self.assertAlmostEqual(out["sum_abs_group_signed"],
                               0.03155665844126213, places=15)
        self.assertAlmostEqual(out["cross_group_signed_over_accumulators"],
                               0.006730753905587463, places=15)
        self.assertEqual(out["groups"], 53)
        self.assertEqual(out["accumulator_rows"], 456)
        self.assertEqual(out["largest_abs_term_record"], 1970)

    def test_small_reference_groups_are_separated_in_the_saved_evidence(self):
        _, out = saved_evidence()
        self.assertEqual(out["groups_flagged_small_reference"], 6)
        self.assertAlmostEqual(out["max_group_ratio_any"],
                               9.356411554531508, places=12)
        self.assertAlmostEqual(
            out["max_group_ratio_excluding_small_reference"],
            0.49597352177221743, places=12)
        self.assertEqual(out["groups_above_10pct_of_accumulator"], 7)

    def test_fortran_subtotal_agrees_with_the_python_subtotal(self):
        """The code's own sum of K*L agrees with the Python SUBTOTAL.

        Not a per-term check: errors in individual weights or local values can
        cancel inside a group subtotal (T-004-R5 item 3).
        """
        _, out = saved_evidence()
        c = out["local_reconstruction_check"]
        self.assertEqual(c["groups_verified"], 53)
        self.assertLess(c["max_relative_difference"], c["limit"])
        self.assertAlmostEqual(c["max_relative_difference"],
                               8.601382692417945e-15, places=18)

    def test_iw_range_follows_the_source_fdf_rule(self):
        """mtxel_cor.f90:514-521 with sig%fdf=2: diag iw in {2,3}, offdiag iw=2."""
        rows = wm.parse(RECORDS.read_text())
        for r in rows:
            with self.subTest(rec=r["rec"]):
                if r["icalc"] == 1:
                    self.assertIn(r["iw"], (2, 3))
                else:
                    self.assertEqual(r["iw"], 2)
        self.assertEqual(sum(1 for r in rows if r["icalc"] == 1), 3336)
        self.assertEqual(sum(1 for r in rows if r["icalc"] == 2), 366)

    def test_generic_clamp_would_not_have_differed(self):
        _, out = saved_evidence()
        self.assertEqual(out["generic_clamp_would_differ"], 0)

    def test_first_48_records_match_the_t003_fixture(self):
        """The T-004 export must preserve the accepted T-003 first-48 values."""
        old = co.parse((ROOT / "bgw" / "occupation_audit" / "fixtures"
                        / "t003_nearpole_occ.dat").read_text())
        new = wm.parse(RECORDS.read_text())[:48]
        self.assertEqual(len(old), 48)
        for o, n in zip(old, new):
            with self.subTest(rec=o["rec"]):
                for field in co.FIELDS:
                    self.assertEqual(o[field], n[field], msg=field)


class MissingFactorStructureTests(unittest.TestCase):
    """Structural, not prose: WHICH factor is missing for WHICH output type.

    The wording of `MISSING_FACTORS` lives in the workflow gate; this asserts
    the physics content -- that `1/ndeg` applies to diagonal outputs only, and
    that `ryd` enters at a different later location for each output type.
    Getting this wrong is a scientific error, not a documentation one.
    """

    def test_missing_factors_structure_is_per_output_type(self):
        mf = wm.MISSING_FACTORS
        self.assertEqual(set(mf), {"both output types",
                                   "diagonal (icalc=1) only",
                                   "offdiagonal (icalc=2) only"})
        self.assertIn("1/ndeg", mf["diagonal (icalc=1) only"])
        self.assertNotIn("1/ndeg", mf["offdiagonal (icalc=2) only"])
        self.assertNotIn("1/ndeg", mf["both output types"])
        # ryd enters at a different later location for each output type
        self.assertIn("shiftenergy", mf["diagonal (icalc=1) only"]["ryd"])
        self.assertIn("sigma_main", mf["offdiagonal (icalc=2) only"]["ryd"])


class FieldReferenceIntegrityTests(unittest.TestCase):
    """Every field-shaped name in an explanatory string must exist.

    Kept on the SCIENTIFIC side when the prose gate was deleted: this is not a
    wording opinion. It is a mechanical self-consistency property of the
    emitted artifact -- the JSON told readers to look at fields that were not
    in it, and shipped that way twice.

    T-004-R5 item 1: the emitted `what` told readers to see `aggregate_note`
    and `cross_output_warning` long after both were renamed, and the saved
    artifact carried the identical text -- so the fresh-vs-saved equality test
    could not see it. Both copies were wrong in the same way. This test checks
    the strings against the object's own key set instead.
    """

    #: snake_case names that legitimately are NOT JSON fields: Fortran symbols,
    #: source paths and run identifiers. Anything added here needs a reason.
    NOT_FIELDS = frozenset({
        "branch_mismatch", "sigma_gpp_cpu", "sigma_main", "mtxel_cor",
        "fermi_level_absolute", "weighted_audit", "occupation_audit",
        "t004_instrument", "t4_b", "t4_o", "check_occupation",
        "weighted_mismatch", "completeness_evidence",
    })
    #: Backticks are STRIPPED, not treated as a boundary that excludes the
    #: token. The first version of this regex excluded backticked names, which
    #: meant the single most common way to write a field reference --
    #: `cross_group_warning` in prose -- was exactly the case it could not see.
    #: That was recorded as a known residual of T-004-R5 and is fixed here.
    TOKEN = re.compile(
        r"(?<![\w`])`?([a-z][a-z0-9]*(?:_[a-z0-9]+)+)`?(?![\w])")

    @staticmethod
    def _keys(obj, acc):
        if isinstance(obj, dict):
            acc.update(obj)
            for v in obj.values():
                FieldReferenceIntegrityTests._keys(v, acc)
        elif isinstance(obj, list):
            for v in obj:
                FieldReferenceIntegrityTests._keys(v, acc)
        return acc

    @staticmethod
    def _strings(obj, acc, path="$"):
        if isinstance(obj, dict):
            for k, v in obj.items():
                FieldReferenceIntegrityTests._strings(v, acc, f"{path}.{k}")
        elif isinstance(obj, list):
            for i, v in enumerate(obj):
                FieldReferenceIntegrityTests._strings(v, acc, f"{path}[{i}]")
        elif isinstance(obj, str):
            acc.append((path, obj))
        return acc

    def _check(self, doc, label):
        keys = self._keys(doc, set())
        dangling = []
        for path, text in self._strings(doc, []):
            for tok in self.TOKEN.findall(text):
                if tok in keys or tok in self.NOT_FIELDS:
                    continue
                dangling.append(f"{label}{path} -> {tok!r}")
        self.assertEqual(dangling, [],
                         "explanatory strings name fields that do not exist "
                         "in the emitted object")

    def test_fresh_output_has_no_dangling_field_references(self):
        _, out = saved_evidence()
        self._check(out, "fresh:")

    def test_saved_artifact_has_no_dangling_field_references(self):
        saved = json.loads(
            (ROOT / "artifacts" / "t004" / "weighted_mismatch.json").read_text())
        self._check(saved, "saved:")

    def test_the_detector_would_have_caught_the_r4_defect(self):
        """A mutation: reintroduce the exact stale reference that shipped."""
        _, out = saved_evidence()
        broken = dict(out)
        broken["what"] = ("see aggregate_note and cross_output_warning.")
        with self.assertRaises(AssertionError):
            self._check(broken, "mutated:")

    def test_the_detector_sees_through_backticks(self):
        """The T-004-R5 residual: a backticked dead field was invisible.

        Prose almost always writes field names in backticks, so the original
        regex was blind in precisely the common case.
        """
        _, out = saved_evidence()
        broken = dict(out)
        broken["what"] = "see `aggregate_note` and `cross_output_warning`."
        with self.assertRaises(AssertionError):
            self._check(broken, "mutated:")

    def test_a_backticked_live_field_is_still_accepted(self):
        """The fix must not make every backticked name a failure."""
        _, out = saved_evidence()
        ok = dict(out)
        ok["what"] = "see `per_call_group_l1_note` and `cross_group_warning`."
        self._check(ok, "mutated:")

    def test_what_points_at_the_current_aggregate_fields(self):
        _, out = saved_evidence()
        self.assertIn("per_call_group_l1_note", out["what"])
        self.assertIn("cross_group_warning", out["what"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
