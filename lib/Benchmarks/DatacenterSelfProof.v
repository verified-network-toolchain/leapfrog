Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.DataCenter.

Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".
SetSMTLang "BV".

Lemma datacenter_self_equiv:
  lang_equiv_state
    (P4A.interp DataCenter.aut)
    (P4A.interp DataCenter.aut)
    DataCenter.ParseEth0
    DataCenter.ParseEth0.
Proof.
  solve_lang_equiv_state_admit DataCenter.state_eqdec DataCenter.state_eqdec true.
Time Admitted.
