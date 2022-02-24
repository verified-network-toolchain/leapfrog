Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Edge.
Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".

Lemma ethernet_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Optimized.aut)
    Plain.ParseEth0
    Optimized.State_0.
Proof.
  solve_lang_equiv_state_axiom Plain.state_eqdec Optimized.state_eqdec true.
Time Qed.