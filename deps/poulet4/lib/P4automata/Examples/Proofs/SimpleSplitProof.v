Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SimpleSplit.
Require Import ZArith List Bool.

From Hammer Require Import Tactics.
From Hammer Require Import Hammer.

Definition possibly_unsound_init_rel
  : crel (Simple.state + Split.state) (Sum.H Simple.header Split.header)
  :=
    (mk_init 100 SimpleSplit.aut Simple.Start Split.StSplit1). 

(*
Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ _ [] _ _ => apply PreBisimulationClose
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: {R ⊨ C} + {~(R ⊨ C)})
      by idtac;
    destruct H;
    [
        let t := fresh "tmp" in
        pose (t := wp a C); apply PreBisimulationExtend with (W := t);
         [ reflexivity |  ]; compute in t; unfold t; clear t;
         simpl (_ ++ _)
  end
*)


Notation i := (separated _ _ _ SimpleSplit.aut).
Notation "⟦ x ⟧" := (interp_crel i x).
Notation "⦇ x ⦈" := (interp_conf_rel (a:=SimpleSplit.aut) x).
Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).

Lemma forall_exists:
  forall {A B} (P: A -> B -> Prop),
  (exists x y, ~ P x y) ->
  ~ (forall x y, P x y).
Proof.
  firstorder.
Qed.

Lemma double_neg: 
  forall {A B} (P: A -> B -> Prop),
  (exists x y, P x y) ->
  (exists x y, ~ (P x y -> False)).
Proof.
  intros.
  destruct H as [x [y H]].
  exists x.
  exists y.
  intuition.
Qed.

Lemma split_univ:
  forall (A B : Type) (P : A * B -> Prop),
    (forall (x : A) (y : B), P (x, y)) <-> (forall x : A * B, P x).
Proof.
  firstorder.
  destruct x.
  firstorder.
Qed.

(* Ltac break_products :=
  match goal with 
  | *)

Lemma exists_unused:
  forall A,
    inhabited A ->  
    forall P: Prop,
    exists (_: A), P <-> P.
Proof.
  intros.
  inversion H.
  firstorder.
Qed.
Lemma flip_ex_impl:
  forall A B (P Q: A -> B -> Prop),
    (exists x y, P x y /\ ~ Q x y) ->
    (exists x y, ~ (P x y -> Q x y)).
Proof.
  firstorder.
Qed.

Definition states_match (c1 c2: conf_rel SimpleSplit.state SimpleSplit.header) : bool :=
  if conf_state_eq_dec c1.(cr_st) c2.(cr_st)
  then true
  else false.

Lemma filter_entails:
  forall R C,
    R ⊨ C <-> filter (states_match C) R ⊨ C.
Proof.
Admitted.

Lemma no_state:
  forall R S,
    (forall q1 q2 (_ : interp_crel (separated _ _ _ SimpleSplit.aut) R q1 q2),
        interp_conf_rel S q1 q2)
    <->
    (forall st1 (buf1: n_tuple bool S.(cr_st).(cs_st1).(st_buf_len)) st2 (buf2: n_tuple bool S.(cr_st).(cs_st2).(st_buf_len)),
        let q1 := (S.(cr_st).(cs_st1).(st_state), st1, t2l _ _ buf1) in
        let q2 := (S.(cr_st).(cs_st2).(st_state), st2, t2l _ _ buf2) in
        interp_crel (separated _ _ _ SimpleSplit.aut) R q1 q2 ->
        forall valu : bval (cr_ctx S), interp_store_rel (cr_rel S) valu q1 q2).
Proof.
  intros.
  unfold "⊨".
  split; intros.
  - unfold interp_conf_rel in *.
    simpl.
    intros.
Admitted.

Ltac disprove_sat :=
  rewrite filter_entails;
  simpl;
  rewrite no_state;
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn);
  eapply forall_exists;
  repeat (setoid_rewrite <- split_univ; cbn);
  repeat (setoid_rewrite <- split_ex; cbn);
  solve [sauto].

Ltac disprove_sat_old :=
  unfold interp_conf_rel;
  simpl;
  eapply forall_exists;
  apply flip_ex_impl;
  unfold "⊨";
  simpl;
  repeat setoid_rewrite <- split_ex;
  simpl;
  unfold interp_conf_state, interp_state_template;
  simpl;
  unfold i;
  repeat (simpl (fst _) || simpl (snd _));
  unfold Sum.H, P4A.store, P4A.Env.t;
  unfold not;
  sauto.

Ltac extend_bisim a wp R C :=
      let H := fresh "H" in
      assert (H: ~(R ⊨ C)) by disprove_sat;
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.

Ltac extend_bisim_old a wp R C :=
      let H := fresh "H" in
      assert (H: ~(R ⊨ C)) by disprove_sat_old;
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.

Ltac prove_sat :=
  unfold interp_conf_rel;
  unfold "⊨";
  unfold interp_conf_state, interp_state_template;
  simpl;
  sauto limit:5000.

Ltac skip_bisim a wp R C :=
  let H := fresh "H" in
  assert (H: R ⊨ C)
    by prove_sat;
  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    extend_bisim a wp R C
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    skip_bisim a wp R C
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  end.

(* Lemma prebisim_simple_split_sym_small_init_leap:
  pre_bisimulation SimpleSplit.aut
                   (WPSymLeap.wp (H:=SimpleSplit.header))
                   (separated _ _ _ SimpleSplit.aut)
                   nil
                   possibly_unsound_init_rel
                   (inl (inl Simple.Start), [], [])
                   (inl (inr Split.StSplit1), [], []).
Proof.
  set (r := possibly_unsound_init_rel).
  cbv in r.
  subst r.
  time repeat (idtac "..."; time solve_bisim).
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template || cbn).
  intuition eauto;
    firstorder (try congruence);
    sauto limit:5000.
Qed. *)

