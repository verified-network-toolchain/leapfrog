Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Notation H := (IPOptionsRef63.header + TimestampSpec3.header).
Notation A := (Sum.sum IPOptionsRef63.aut TimestampSpec3.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := IPOptionsRef63.Parse0.
Notation start_right := TimestampSpec3.Parse0.


Definition r_states' := (Reachability.reachable_states
                          A
                          9
                          start_left
                          start_right).

Definition r_states := Eval vm_compute in r_states'.

Definition top : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) r_states.

Definition top' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) r_states.

Definition top'' : Relations.rel conf :=
  fun q1 q2 => List.In (conf_to_state_template q1, conf_to_state_template q2) r_states'.

Definition top''' : Relations.rel (state_template A) :=
  fun q1 q2 => List.In (q1, q2) r_states'.

Lemma r_states_conv:
  r_states = r_states'.
Proof.
  exact eq_refl.
Qed.

Lemma top_conv:
  forall q1 q2, top q1 q2 <-> top'' q1 q2.
Proof.
  intros; unfold top, top''; erewrite r_states_conv; eapply iff_refl.
Qed.

Lemma top'_conv:
  forall q1 q2, top' q1 q2 <-> top''' q1 q2.
Proof.
  intros; unfold top', top'''; erewrite r_states_conv; eapply iff_refl.
Qed.

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
                   (wp r_states)
                   top
                   []
                   (mk_init _ _ _ A 9 start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp three bisimulation".
  intros.
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).

  eapply PreBisimulationClose;
  match goal with
  | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ ?top ?P ?q1 ?q2 =>
    let H0 := fresh "H0" in
    assert (H0: interp_entailment' top {| e_prem := P; e_concl := C |}) by (
      eapply simplify_entailment_correct' with (i := top');
      eapply compile_simplified_entailment_correct';

      simpl; intros;
      eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
      eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;

      crunch_foterm;
      match goal with
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    );
    eapply H0;
    destruct q1, q2;
    vm_compute in H;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    end;
    [
      (* apply in_checker_conv with (A_eq := fun x y => state_temp_prod_eqdec x y);
      unfold conf_to_state_template, P4automaton.conf_buf_len, P4automaton.conf_state;

      repeat match goal with
      | H: _ = _ |- _ => erewrite <- H
      end;
      exact eq_refl *)
                    |
      split; [ vm_compute; (repeat split || assumption) | (intros; exact I)]
    ]
  end.
  eapply top_conv.
  unfold top''.
  eapply Reachability.reachable_states_triv.
  left.
  subst.
  exact eq_refl.

Time Admitted.
