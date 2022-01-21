Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SelfComparison.


Declare ML Module "mirrorsolve".

SetSMTSolver "cvc4".

Module Positive.

  Notation H := (ReadUndef.header + ReadUndef.header).
  Notation A := (Sum.sum ReadUndef.aut ReadUndef.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Notation start_left := (ReadUndef.ParseEth).
  Notation start_right := (ReadUndef.ParseEth).

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

  ClearEnvCtors.

  Lemma prebisim_babyip:
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
    idtac "running self-comparison positive bisimulation".

    intros.

    pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

    unfold mk_init.
    rewrite Hr.
    clear Hr.
    
    set (foo := (List.nodup (conf_rel_eq_dec (a:=A)) (mk_partition _ _ _ _ _ _))).
    vm_compute in foo.
    subst foo.

    time "build phase" repeat (time "single step" run_bisim top top' (projT1 r_states)).
    time "close phase" close_bisim top'.
  Time Admitted.
End Positive.

Module Negative.

  Notation H := (ReadUndefIncorrect.header + ReadUndefIncorrect.header).
  Notation A := (Sum.sum ReadUndefIncorrect.aut ReadUndefIncorrect.aut).
  Notation conf := (P4automaton.configuration (P4A.interp A)).
  Notation start_left := (ReadUndefIncorrect.ParseEth).
  Notation start_right := (ReadUndefIncorrect.ParseEth).

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

  ClearEnvCtors.

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
                    (wp (projT1 r_states))
                    top
                    []
                    (mk_init _ _ _ _ A start_left start_right)
                    q1 q2.
  Proof.
    idtac "running self-comparison negative bisimulation".

    intros. 

    pose proof (Reachability.reachable_states_wit_conv init_states_wf (projT2 r_states)) as Hr.

    unfold mk_init.
    rewrite Hr.
    clear Hr.
    
    set (foo := (List.nodup (conf_rel_eq_dec (a:=A)) (mk_partition _ _ _ _ _ _))).
    vm_compute in foo.
    subst foo.

    time "build phase" repeat (time "single step" run_bisim top top' (projT1 r_states)).
    Fail time "close phase" close_bisim top'.
  Time Admitted.
End Negative.
