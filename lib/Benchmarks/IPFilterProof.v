Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPFilter.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".

Lemma ipfilter_equiv:
  lang_equiv_state
    (P4A.interp UDPCombined.aut)
    (P4A.interp UDPInterleaved.aut)
    UDPCombined.ParsePref
    UDPInterleaved.ParseIP.
Proof.
  solve_lang_equiv_state UDPCombined.state_eqdec UDPInterleaved.state_eqdec.
Time Qed.
