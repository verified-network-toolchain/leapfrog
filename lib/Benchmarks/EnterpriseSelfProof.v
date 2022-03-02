Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Enterprise.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".

Lemma enterprise_self_equiv:
  lang_equiv_state
    (P4A.interp Simple.aut)
    (P4A.interp Simple.aut)
    Simple.ParseEth
    Simple.ParseEth.
Proof.
  solve_lang_equiv_state_admit Simple.state_eqdec Simple.state_eqdec true.
Time Admitted.

