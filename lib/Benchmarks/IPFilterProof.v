Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPFilter.

Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".

Ltac decide_entailment_axiom H P HP el er P_orig e :=
  let Horig := fresh "Horig" in
  pose (P_orig := e);
  time "remembering iff" remember_iff P HP e;
  time "Horig" assert (Horig: P_orig <-> P)
    by (rewrite HP; eapply iff_refl);
  time "compile fm" compile_fm HP el er.

Lemma ipfilter_equiv:
  lang_equiv_state
    (P4A.interp UDPCombined.aut)
    (P4A.interp UDPInterleaved.aut)
    UDPCombined.ParsePref
    UDPInterleaved.ParseIP.
Proof.
  solve_lang_equiv_state_axiom UDPCombined.state_eqdec UDPInterleaved.state_eqdec false.
Time Qed.
