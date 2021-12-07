Require Import Coq.Lists.List.
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
          length buf = Leaps.leap_size _ q1 q2 ->
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
    forall q1 q2 bs,
        length bs = Leaps.leap_size _ q1 q2 ->
        R q1 q2 /\ T q1 q2 ->
        R (follow q1 bs) (follow q2 bs).

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
        constructor 1.
        eapply H0; eauto.
        split; simpl; eauto.
        eapply interp_rels_bound; eauto.
    - assert (coaccepting (⟦ R ⟧ ⊓ ⟦ T ⟧)).
      {
        unfold coaccepting; intros.
        apply H.
        destruct H3.
        repeat split; auto.
      }
      assert (follow_closed ⟦ R ⟧ ⟦ T ⟧).
      {
        unfold follow_closed; intros.
        destruct H5.
        apply H0; auto.
        repeat split; eauto.
      }
      split.
      + apply IHpre_bisimulation; auto.
      + intros.
        constructor 2; auto.
        apply IHpre_bisimulation; eauto.
    - assert (coaccepting (⟦C :: R⟧ ⊓ ⟦W ++ T⟧)).
      {
        unfold coaccepting; intros.
        apply H.
        destruct H4.
        apply app_interp_rels in H5; destruct H5.
        simpl in H4; destruct H4.
        repeat split; auto.
      }
      assert (follow_closed ⟦C::R⟧ ⟦W++T⟧).
      {
        unfold follow_closed.
        unfold follow_closed in H0.
        intros.
        destruct H6.
        apply app_interp_rels in H7.
        destruct H6, H7.
        repeat split.
        - eapply H3; eauto.
        - apply H0; eauto.
          repeat split; eauto.
      }
      split.
      + apply IHpre_bisimulation; eauto.
      + intros.
        econstructor 3; eauto.
        eapply IHpre_bisimulation; eauto.
  Qed.

  Lemma algorithmic_leaps_implies_bisimilar_leaps:
    forall R T q1 q2,
      coaccepting (⟦R⟧ ⊓ ⟦T⟧) ->
      follow_closed ⟦R⟧ ⟦T⟧ ->
      pre_bisimulation a top R T q1 q2 ->
      Leaps.bisimilar_with_leaps a q1 q2.
  Proof.
    intros.
    eauto using bisimilar_is_bisimulation,
                pre_bisimulation_is_bisimulation.
  Qed.

End AlgorithmicLeaps.
