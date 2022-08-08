Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPOptions.
Require Import Leapfrog.Benchmarks.Timestamp.

Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".
SetSMTLang "BV".

Lemma ipoptions3_equiv:
  lang_equiv_state
    (P4A.interp IPOptionsRef63.aut)
    (P4A.interp TimestampSpec3.aut)
    IPOptionsRef63.Parse1
    TimestampSpec3.Parse1.
Proof.
  solve_lang_equiv_state_admit IPOptionsRef63.state_eqdec TimestampSpec3.state_eqdec true.
Time Admitted.
