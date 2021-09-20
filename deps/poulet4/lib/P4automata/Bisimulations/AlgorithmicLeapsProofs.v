Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeaps.

Section AlgorithmicLeaps.
  Variable (a: p4automaton).
  Notation conf := (configuration a).
  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_rels top x).
  Notation "R ⊨ S" := (forall q1 q2,
                          ⟦R⟧ q1 q2 ->
                          S q1 q2)
                        (at level 40).

  Definition bisimulation_with_leaps (R: rel conf) :=
    forall q1 q2 : configuration a,
      R q1 q2 ->
      (accepting q1 <-> accepting q2) /\
      (forall buf : list bool,
          length buf = Nat.min (configuration_room_left q1) (configuration_room_left q2) ->
          R (follow q1 buf) (follow q2 buf)).

  Lemma bisimilar_is_bisimulation:
    forall R q1 q2,
      bisimulation_with_leaps R ->
      R q1 q2 ->
      Leaps.bisimilar_with_leaps a q1 q2.
  Proof.
    cofix C.
    intros.
    constructor.
    - specialize (H q1 q2 H0).
      tauto.
    - intros.
      eapply C with (R:=R); auto.
      apply H; eauto.
  Qed.

  Definition follow_closed (R T: rel conf) : Prop :=
    forall q1 q2,
      R q1 q2 ->
      forall bs,
        length bs = Nat.min (configuration_room_left q1)
                            (configuration_room_left q2) ->
        (relation_conjunction R T) (follow q1 bs) (follow q2 bs).

  Definition coaccepting (R: rel conf) : Prop :=
    forall q1 q2,
      R q1 q2 ->
      (accepting q1 <-> accepting q2).

  Lemma pre_bisimulation_is_bisimulation:
    forall R T,
      coaccepting (⟦R⟧ ⊓ ⟦T⟧) ->
      follow_closed ⟦R⟧ ⟦T⟧ ->
      bisimulation_with_leaps (pre_bisimulation a top R T).
  Proof.
    unfold bisimulation_with_leaps.
    intros.
    induction H1.
    - split.
      + apply H; split; auto.
        simpl.
        eapply interp_rels_bound; eauto.
      + intros.
        constructor.
        unfold follow_closed in H0.
        apply H; auto.
    - split.
      + apply H; split; auto.
        simpl.
        eapply interp_rels_bound; eauto.
      + admit.
      + intros.
        unfold follow_closed in H.
        constructor 2.
        auto.
        apply IHpre_bisimulation; auto.
        unfold follow_closed; intros.
        split; eapply H; eauto.
    - split.
      + admit.
      + intros.
        unfold follow_closed in H.
        econstructor 3.
        * eauto.
        * eapply IHpre_bisimulation; auto.
          unfold follow_closed; intros.
          destruct H4.
          repeat split; eauto.
          -- eapply H; eauto.
          -- eapply H; eauto.
          -- eapply interp_rels_app; try solve [eapply H; eauto].
             admit.
        * intros.
          eapply H2; eauto.
  Admitted.
  
  Lemma algorithmic_leaps_implies_bisimilar_leaps:
    forall R T q1 q2,
      pre_bisimulation a top R T q1 q2 ->
      Leaps.bisimilar_with_leaps a q1 q2.
  Proof.
    intros.
    eapply bisimilar_is_bisimulation.
    cofix C.
    constructor.
    induction H.
    - 
    - cofix C.
    constructor.
    - inversion H0.
    - 
  Abort.
  
End AlgorithmicLeaps.
