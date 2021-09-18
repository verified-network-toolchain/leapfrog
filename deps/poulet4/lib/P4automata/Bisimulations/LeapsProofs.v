Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4automata.Bisimulations.Upto.
Require Poulet4.P4automata.Bisimulations.UptoProofs.
Require Import Poulet4.P4automata.Bisimulations.Leaps.
Require Poulet4.P4automata.Bisimulations.Semantic.
Module BS := Poulet4.P4automata.Bisimulations.Semantic.
Require Poulet4.P4automata.Bisimulations.SemanticCoinductive.
Module BC := Poulet4.P4automata.Bisimulations.SemanticCoinductive.

Section LeapsProofs.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Program Instance close_interpolate_sound
    : Upto.SoundClosure a (close_interpolate a).
  Next Obligation.
    eauto using InterpolateBase.
  Qed.
  Next Obligation.
    induction H0; eauto.
    unfold configuration_has_room in H1, H2.
    repeat (unfold step; destruct (le_lt_dec _ _); try lia).
    unfold accepting; simpl.
    subst; easy.
  Qed.
  Next Obligation.
    revert b; induction H0; intros; eauto.
    destruct (le_lt_dec (Nat.min (configuration_room_left q1)
                                 (configuration_room_left q2)) 2).
    - apply InterpolateBase.
      replace (step (step q1 b) b0) with (follow q1 [b; b0]) by auto.
      replace (step (step q2 b) b0) with (follow q2 [b; b0]) by auto.
      apply H5; simpl.
      unfold configuration_room_left in *.
      unfold configuration_has_room in H1, H2.
      lia.
    - unfold configuration_room_left in *.
      eapply InterpolateStep with (s1 := s1) (s2 := s2); auto.
      + unfold configuration_has_room, step.
        destruct (le_lt_dec _ _); simpl; lia.
      + unfold configuration_has_room, step.
        destruct (le_lt_dec _ _); simpl; lia.
      + unfold step.
        destruct (le_lt_dec _ _); try lia.
        easy.
      + unfold step.
        destruct (le_lt_dec _ _); try lia.
        easy.
      + intros.
        repeat rewrite <- follow_equation_2.
        apply H5; simpl.
        unfold configuration_room_left in H6.
        rewrite H6; unfold step.
        repeat (destruct (le_lt_dec _ _)); simpl; lia.
  Qed.
  Next Obligation.
    induction H0.
    - eauto using InterpolateBase.
    - eauto using InterpolateStep.
  Qed.

  Lemma bisimilar_with_leaps_implies_bisimilar_upto
        (c1 c2: conf)
    :
      bisimilar_with_leaps a c1 c2 ->
      Upto.bisimilar_upto a (close_interpolate a) c1 c2
  .
  Proof.
    intros.
    exists (bisimilar_with_leaps a).
    split; auto.
    intros c1' c2' ?; split; [now inversion H0|].
    intros.
    destruct (conf_state c1') eqn:?;
    destruct (conf_state c2') eqn:?.
    - destruct (le_lt_dec 2 (min (configuration_room_left c1')
                                 (configuration_room_left c2'))).
      + unfold configuration_room_left in *.
        eapply InterpolateStep with (s1 := s) (s2 := s0); auto.
        * unfold configuration_has_room in *; lia.
        * unfold configuration_has_room in *; lia.
        * now apply InterpolateBase.
        * now inversion H0.
      + rewrite <- follow_equation_1.
        rewrite <- follow_equation_1 at 1.
        repeat rewrite <- follow_equation_2.
        inversion H0.
        apply InterpolateBase, H2; auto; simpl.
        unfold configuration_room_left in *.
        destruct c1', c2'; simpl in *.
        lia.
    - rewrite <- follow_equation_1.
      rewrite <- follow_equation_1 at 1.
      repeat rewrite <- follow_equation_2.
      inversion H0.
      clear H0.
      subst.
      apply InterpolateBase, H2; auto; simpl.
      unfold configuration_room_left.
      destruct c1', c2'; simpl in *; subst.
      cbn in *.
      clear H2 H1.
      autorewrite with size' in *.
      lia.
    - rewrite <- follow_equation_1.
      rewrite <- follow_equation_1 at 1.
      repeat rewrite <- follow_equation_2.
      inversion H0; clear H0; subst.
      apply InterpolateBase, H2; auto; simpl.
      unfold configuration_room_left.
      clear H1 H2.
      destruct c1', c2'; simpl in *; subst.
      autorewrite with size' in *.
      lia.
    - rewrite <- follow_equation_1.
      rewrite <- follow_equation_1 at 1.
      repeat rewrite <- follow_equation_2.
      inversion H0; clear H0; subst.
      apply InterpolateBase, H2; auto; simpl.
      unfold configuration_room_left.
      clear H1 H2.
      destruct c1', c2'; simpl in *; subst.
      autorewrite with size' in *.
      lia.
  Qed.

  Lemma bisimilar_implies_bisimilar_with_leaps:
    forall c1 c2,
      BC.bisimilar a c1 c2 ->
      bisimilar_with_leaps a c1 c2
  .
  Proof.
    cofix C.
    intros.
    constructor.
    - inversion H.
      congruence.
    - intros.
      apply C.
      clear H0.
      induction buf using rev_ind.
      + autorewrite with follow.
        exact H.
      + rewrite !follow_append.
        inversion IHbuf.
        eauto.
  Qed.

  Theorem bisimilar_iff_bisimilar_with_leaps
          (c1 c2: conf)
    :
      BS.bisimilar a c1 c2 <->
      bisimilar_with_leaps a c1 c2
  .
  Proof.
    split; intro.
    - apply bisimilar_implies_bisimilar_with_leaps.
      now apply BC.sem_bisim_implies_bisimilar_coalg.
    - eapply UptoProofs.bisimilar_upto_implies_bisimilar.
      + apply close_interpolate_sound.
      + now apply bisimilar_with_leaps_implies_bisimilar_upto.
  Qed.

End LeapsProofs.
