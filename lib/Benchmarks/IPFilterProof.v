Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPFilter.

Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".
SetSMTLang "BV".

Lemma ipfilter_equiv:
  lang_equiv_state
    (P4A.interp UDPCombined.aut)
    (P4A.interp UDPInterleaved.aut)
    UDPCombined.ParsePref
    UDPInterleaved.ParseIP.
Proof.
  solve_lang_equiv_state_axiom UDPCombined.state_eqdec UDPInterleaved.state_eqdec false.
Time Qed.
