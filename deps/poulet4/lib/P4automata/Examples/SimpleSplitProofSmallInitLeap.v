Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.SimpleSplit.

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
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    assert (~(R ⊨ C))
  end.
  {
    repeat (unfold interp_crel,
            interp_conf_rel,
            interp_conf_state,
            interp_store_rel,
            interp_bit_expr,
            interp_store_rel,
            interp_state_template,
            RelationClasses.relation_conjunction,
            Relations.interp_rels,
            separated
            || cbn).
    match goal with
    | |- ~ (forall x y: ?T, @?Q x y) =>
      eapply forall_exists with (P := Q)
    end.
    unfold P4automaton.configuration.
    simpl.
    unfold P4A.store, P4A.Env.t, Sum.H in *.
    pose (l := [false;false;false;false;
                false;false;false;false]).
    assert (length l = 8) by reflexivity.
    pose (t := Simple.Start).
    pose (t' := Split.StSplit1).
    pose (t'' := Split.StSplit2).
    Import Tactics.
    hfcrush.
    Tactics.sfirstorder.
    Hammer.hammer.
    sfirstorder.
    
      idtac P;
      eapply forall_exists; try eapply H
    end.
    Hammer.hammer.
    do 2 destruct H0.
    eapply H0.
    specialize (H (inl (inl Simple.Start), [], [false;false;false;false;false;false;false;false]) (inr true, [], []));
    intuition.
             : {R ⊨ C} + {~(R ⊨ C)} 
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    set (H := ltac:(
                right;
    repeat (unfold interp_crel,
            interp_conf_rel,
            interp_conf_state,
            interp_store_rel,
            interp_bit_expr,
            interp_store_rel,
            interp_state_template,
            RelationClasses.relation_conjunction,
            Relations.interp_rels,
            separated
            || cbn);
    intuition;
    simpl in *;
    Hammer.hammer
    specialize (H (inl (inl Simple.Start), [], [false;false;false;false;false;false;false;false]) (inr true, [], []));
    intuition
             )
             : {R ⊨ C} + {~(R ⊨ C)} 
        )
  end.
  eapply PreBisimulationExtend with (H0:=H); eauto.
  exact I.
  clear H.
  cbn.
  simpl (_ ++ _).
  cbv.
  solve_bisim'.
  time (repeat solve_bisim').
  cbv in *.
  intuition (try congruence).
Qed.
