Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Ethernet.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".


Lemma ethernet_equiv:
  lang_equiv_state
    (P4A.interp Reference.aut)
    (P4A.interp Combined.aut)
    Reference.SPref
    Combined.Parse.
Proof.
  eapply lang_equiv_to_pre_bisim;
  time "init prebisim" (intros;
  unfold mk_init;
  erewrite Reachability.reachable_states_wit_conv; [
    | repeat econstructor
    | unfold Reachability.reachable_states_wit;
      solve_fp_wit
  ]; simpl).
Admitted.
  (* solve_lang_equiv_state_axiom Reference.state_eqdec Combined.state_eqdec false.
Time Qed. *)
