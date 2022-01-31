Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.DataCenter.

Require Import Coq.Arith.PeanoNat.


Declare ML Module "mirrorsolve".

Notation H := (DataCenter.header + DataCenter.header).
Notation A := (Sum.sum DataCenter.aut DataCenter.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := (DataCenter.ParseEth0).
Notation start_right := (DataCenter.ParseEth0).

SetSMTSolver "cvc4".


Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

Lemma init_states_wf:
  Reachability.valid_state_pair (Reachability.build_state_pair A start_left start_right).
Proof.
  vm_compute; Lia.lia.
Qed.

Lemma prebisim_babyip:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl start_left);
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr start_right);
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                  |} q1 q2 ->
  pre_bisimulation A
                   (projT1 r_states)
                   (wp (a := A))
                   []
                   (mk_init _ _ _ _ A start_left start_right)
                   q1 q2.
Proof.
  idtac "running datacenter self-comparison bisimulation".

  intros.

  pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

  unfold mk_init.
  rewrite Hr.
  clear Hr.

  set (rel0 := (List.nodup _) (mk_partition _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim).
  time "close phase" close_bisim.
Time Admitted.
