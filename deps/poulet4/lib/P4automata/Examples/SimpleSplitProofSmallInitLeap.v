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

Ltac disprove_sat :=
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
  sauto limit:5000.

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

Ltac skip_bisim a wp R C :=
  let H := fresh "H" in
  assert (H: R ⊨ C)
    by (unfold interp_conf_rel;
        unfold "⊨";
        unfold interp_conf_state, interp_state_template;
        simpl;
        sauto limit:5000);
        eapply PreBisimulationSkip with (H0:=left H);
        clear H.
        (* 
        [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template in *;
        simpl in *;
        subst;
        intros;
        intuition;
        repeat 
          match goal with
          | [ X : P4automaton.configuration _ |- _ ] => destruct X as [[? ?] l]; destruct l
          | [ X : _ * _ |- _ ] => destruct X
          end;
          simpl in *; try solve [simpl in *; congruence]
          |]. *)

Ltac solve_bisim :=
  match goal with
  (* | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    skip_bisim a wp R C *)
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    extend_bisim a wp R C
  (* | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose *)
  end.

Lemma prebisim_simple_split_sym_small_init_leap:
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
  solve_bisim.
  match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    skip_bisim a wp R C; auto
  end.
  (* proof goal for ~(R |= C) in 1st step
  exists x y : P4automaton.configuration (P4A.interp SimpleSplit.aut),
    i x y /\
    (((exists t1 t2 : unit * bool * bool * bool * bool * bool * bool * bool * bool,
         [snd (fst (fst (fst (fst (fst (fst (fst t1)))))));
         snd (fst (fst (fst (fst (fst (fst t1))))));
         snd (fst (fst (fst (fst (fst t1))))); snd (fst (fst (fst (fst t1))));
         snd (fst (fst (fst t1))); snd (fst (fst t1)); 
         snd (fst t1); snd t1] = snd x /\
         [snd (fst (fst (fst (fst (fst (fst (fst t2)))))));
         snd (fst (fst (fst (fst (fst (fst t2))))));
         snd (fst (fst (fst (fst (fst t2))))); snd (fst (fst (fst (fst t2))));
         snd (fst (fst (fst t2))); snd (fst (fst t2)); 
         snd (fst t2); snd t2] = snd y /\
         inl (inl Simple.Start) = fst (fst x) /\ inr true = fst (fst y)) ->
      unit -> False) -> False)
   *)
  (* proof goal for ~(R |= C) in 3rd step
  exists x y : P4automaton.configuration (P4A.interp SimpleSplit.aut),
    (((exists t1 t2 : unit * bool * bool * bool * bool * bool * bool * bool * bool,
         [snd (fst (fst (fst (fst (fst (fst (fst t1)))))));
         snd (fst (fst (fst (fst (fst (fst t1))))));
         snd (fst (fst (fst (fst (fst t1))))); snd (fst (fst (fst (fst t1))));
         snd (fst (fst (fst t1))); snd (fst (fst t1)); 
         snd (fst t1); snd t1] = snd x /\
         [snd (fst (fst (fst (fst (fst (fst (fst t2)))))));
         snd (fst (fst (fst (fst (fst (fst t2))))));
         snd (fst (fst (fst (fst (fst t2))))); snd (fst (fst (fst (fst t2))));
         snd (fst (fst (fst t2))); snd (fst (fst t2)); 
         snd (fst t2); snd t2] = snd y /\
         inl (inl Simple.Start) = fst (fst x) /\ inr true = fst (fst y)) ->
      unit -> False) /\ i x y) /\
    (((exists _ _ : unit,
         [] = snd x /\
         [] = snd y /\
         inl (inl Simple.Start) = fst (fst x) /\
         inl (inr Split.StSplit2) = fst (fst y)) ->
      unit * {b : list bool | length b = 8} -> False) -> False)

   *)
  match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(R ⊨ C))
  end.
  {
    repeat (unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template || cbn).
    eapply forall_exists.
    apply flip_ex_impl.
    unfold not.
    repeat setoid_rewrite <- split_ex.
    cbn.
    unfold i.
    repeat (simpl (fst _) || simpl (snd _)).
    unfold Sum.H, P4A.store, P4A.Env.t.
    unfold not.
    assert (
  exists
    (x : Simple.state + Split.state + bool) 
  (y0 : list bool) (x0 : Simple.state + Split.state + bool) 
   (y2 : list bool),
    (((exists
          (y3 y4 y5 y6 y7 y8 y9 y10 : bool)  
       (y11 y12 y13 y14 y15 y16 y17 y18 : bool),
         [y3; y4; y5; y6; y7; y8; y9; y10] = y0 /\
         [y11; y12; y13; y14; y15; y16; y17; y18] = y2 /\
         inl (inl Simple.Start) = x /\ inr true = x0) -> 
      unit -> False) /\
     ((exists x1 : Simple.state, x = inl (inl x1)) \/
      (exists y3 : bool, x = inr y3)) /\
     ((exists x1 : Split.state, x0 = inl (inr x1)) \/
      (exists y3 : bool, x0 = inr y3))) /\
    (((
         [] = y0 /\
         [] = y2 /\ inl (inl Simple.Start) = x /\ inl (inr Split.StSplit2) = x0) ->
      False) -> False)
      ).
    sauto exh:on limit:2000.
    repeat eexists.
    exact nil.
    exact nil.
    - intros.
      repeat destruct H.
      destruct H0.
      destruct H0.
      admit.
    - admit.
    - admit.
    - intro H.
      apply H.
      exists tt. 
      exists tt. 
      eauto.
      pose tt.
      split; eauto.
      exists [false;false;false;false;
         false;false;false;false].
      reflexivity.
  }

  }
  
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.
  match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    skip_bisim a wp R C; auto
  end.
  solve_bisim.
  skip_bisim.

  exact I.
  
    assert (H: R ⊨ C)
  end; [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template, i in *;
        simpl in *|].
  
      (* subst;
      intros;
      repeat 
        match goal with
        | [ X : P4automaton.configuration _ |- _ ] => destruct X as [[? ?] l]; destruct l
        | [ X : _ * _ |- _ ] => destruct X
        | [ X : _ /\ _ |- _ ] => destruct X
        | [ X : exists _, _ |- _ ] => destruct X
        end;
        congruence || intuition
        |]. *)
  admit.
Admitted.
