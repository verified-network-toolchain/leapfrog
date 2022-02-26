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
  eapply lang_equiv_to_pre_bisim.
  time "init prebisim" intros;
  unfold mk_init;
  erewrite Reachability.reachable_states_wit_conv.
  2: repeat time "constructor" econstructor.
  2: unfold Reachability.reachable_states_wit;
     solve_fp_wit.
Time Admitted.