Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.IPOptions.
Require Import Leapfrog.Benchmarks.Timestamp.

Require Import Coq.Arith.PeanoNat.

Notation H := (IPOptionsRef63.header + TimestampSpec3.header).
Notation A := (Sum.sum IPOptionsRef63.aut TimestampSpec3.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := IPOptionsRef63.Parse0.
Notation start_right := TimestampSpec3.Parse0.

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


Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".

Lemma prebisim_incremental_sep:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (start_left));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (start_right));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (wp (projT1 r_states))
                   top
                   []
                   (mk_init _ _ _ _ A start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp three bisimulation".

  intros.

  pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

  unfold mk_init.
  rewrite Hr.
  clear Hr.
  
  set (foo := (List.nodup (conf_rel_eq_dec (a:=A)) (mk_partition _ _ _ _ _ _))).
  vm_compute in foo.
  subst foo.

  idtac "put the init_rel together".

  time "build phase" repeat (run_bisim top top' (projT1 r_states)).
  time "close phase" close_bisim top'.

Time Admitted.
