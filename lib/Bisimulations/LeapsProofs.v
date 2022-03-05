Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.Bisimulations.Upto.
Require Leapfrog.Bisimulations.UptoProofs.
Require Import Leapfrog.Bisimulations.Leaps.
Require Leapfrog.Bisimulations.Semantic.
Module BS := Leapfrog.Bisimulations.Semantic.
Require Leapfrog.Bisimulations.SemanticCoinductive.
Module BC := Leapfrog.Bisimulations.SemanticCoinductive.

Section LeapsProofs.
  Variable (a: p4automaton).
  Notation conf := (configuration a).

  Lemma config_room_left_nonzero:
    forall q: conf,
      configuration_room_left q > 0.
  Proof.
    intros.
    destruct q.
    unfold configuration_room_left.
    destruct conf_state;
      cbn in *;
      autorewrite with size' in *;
      lia.
  Qed.

  Lemma config_room_left_bound:
    forall q: conf,
      configuration_room_left q <= size' a (conf_state q).
  Proof.
    intros.
    unfold configuration_room_left.
    lia.
  Qed.

  Lemma leap_size_nonzero:
    forall (q1 q2: conf),
      leap_size _ q1 q2 > 0.
  Proof.
    unfold leap_size.
    intros.
    pose proof (config_room_left_nonzero q1).
    pose proof (config_room_left_nonzero q2).
    destruct (conf_state q1), (conf_state q2);
      lia.
  Qed.

  Lemma state_stable:
    forall bs (q: conf),
      length bs < configuration_room_left q ->
      conf_state (follow q bs) = conf_state q.
  Proof.
    induction bs; intros; cbn; autorewrite with follow.
    - auto.
    - unfold step.
      destruct (le_lt_dec _ _).
      + exfalso.
        unfold configuration_room_left in *; simpl in *.
        lia.
      + cbn.
        rewrite IHbs; auto.
        unfold configuration_room_left in *; simpl in *.
        lia.
  Qed.

  Lemma leap_size_step:
    forall (q1 q2: conf) b,
      leap_size a q1 q2 > 1 ->
      leap_size a q1 q2 = 1 + leap_size a (step q1 b) (step q2 b).
  Proof.
    unfold leap_size.
    intros.
    destruct (conf_state q1) eqn:?, (conf_state q2) eqn:?;
             simpl in *;
      unfold configuration_room_left in *.
    - unfold step; simpl.
      destruct (le_lt_dec _ _); try lia.
      simpl.
      rewrite Heqs.
      destruct (le_lt_dec _ _); try lia.
      simpl.
      rewrite Heqs0.
      pose proof (conf_buf_sane q1).
      pose proof (conf_buf_sane q2).
      pose proof (cap a s).
      pose proof (cap a s0).
      rewrite Heqs, Heqs0 in *.
      autorewrite with size' in *.
      lia.
    - assert (conf_state (step q2 b) = inr false)
        by eauto using conf_state_step_done.
      rewrite H0.
      unfold step; simpl.
      destruct (le_lt_dec _ _); try lia.
      simpl.
      rewrite Heqs.
      pose proof (conf_buf_sane q1).
      pose proof (conf_buf_sane q2).
      pose proof (cap a s).
      rewrite Heqs in *.
      lia.
    - assert (conf_state (step q1 b) = inr false)
        by eauto using conf_state_step_done.
      rewrite H0.
      unfold step; simpl.
      destruct (le_lt_dec _ _); try lia.
      simpl.
      rewrite Heqs0.
      pose proof (conf_buf_sane q1).
      pose proof (conf_buf_sane q2).
      pose proof (cap a s).
      rewrite Heqs0 in *.
      lia.
    - lia.
  Qed.

  (* The interpolation operator is a sound up-to principle, which means that
     bisimulations up-to this operator are contained in bisimulations. *)
  Program Instance close_interpolate_sound
    : Upto.SoundClosure a (close_interpolate a).
  Next Obligation.
    unfold Upto.closure_extends; intros.
    eauto using InterpolateBase.
  Qed.
  Next Obligation.
    unfold Upto.closure_preserves_accept; intros.
    induction H0; eauto.
    unfold accepting in *; simpl in *.
    destruct (conf_state q1) as [s1|[|]] eqn:?, (conf_state q2) as [s2|[|]] eqn:?;
      try intuition congruence.
    - destruct (PeanoNat.Nat.eq_dec (leap_size a q1 q2) 1).
      + rewrite e in H1.
        eapply H.
        replace (step q1 b) with (follow q1 [b]) by reflexivity.
        replace (step q2 b) with (follow q2 [b]) by reflexivity.
        eapply H1.
        reflexivity.
      + assert (leap_size a q1 q2 > 1).
        {
          pose proof (leap_size_nonzero q1 q2).
          lia.
        }
        unfold leap_size in H2.
        rewrite Heqs, Heqs0 in H2.
        assert (configuration_room_left q1 > 1)
          by lia.
        assert (configuration_room_left q2 > 1)
          by lia.
        assert (conf_state (step q1 b) = conf_state q1).
        {
          replace (step q1 b) with (follow q1 [b]) by reflexivity.
          apply state_stable.
          simpl.
          lia.
        }
        assert (conf_state (step q2 b) = conf_state q2).
        {
          replace (step q2 b) with (follow q2 [b]) by reflexivity.
          apply state_stable.
          simpl.
          lia.
        }
        intuition congruence.
    - assert (forall buf,
                 length buf = leap_size a q1 q2 ->
                 conf_state (follow q1 buf) = inr true <->
                 conf_state (follow q2 buf) = inr true)
        by eauto.
      destruct (PeanoNat.Nat.eq_dec (configuration_room_left q1) 1).
      + assert (Hleap: leap_size a q1 q2 = 1).
        {
          unfold leap_size.
          rewrite Heqs, Heqs0.
          auto.
        }
        replace (step q1 b) with (follow q1 [b]) by reflexivity.
        replace (step q2 b) with (follow q2 [b]) by reflexivity.
        eapply H2.
        rewrite Hleap.
        reflexivity.
      + assert (configuration_room_left q1 > 1).
        {
          pose proof (config_room_left_nonzero q1).
          lia.
        }
        assert (conf_state (step q1 b) = conf_state q1).
        {
          replace (step q1 b) with (follow q1 [b]) by reflexivity.
          apply state_stable.
          simpl.
          lia.
        }
        rewrite H4.
        replace (conf_state (step q2 b)) with (@inr (states a) _ false)
          by (symmetry; eauto using conf_state_step_done).
        intuition congruence.
    - erewrite !conf_state_step_done by eauto.
      tauto.
    - assert (forall buf,
                 length buf = leap_size a q1 q2 ->
                 conf_state (follow q1 buf) = inr true <->
                 conf_state (follow q2 buf) = inr true)
        by eauto.
      destruct (PeanoNat.Nat.eq_dec (configuration_room_left q2) 1).
      + assert (Hleap: leap_size a q1 q2 = 1).
        {
          unfold leap_size.
          rewrite Heqs, Heqs0.
          auto.
        }
        replace (step q1 b) with (follow q1 [b]) by reflexivity.
        replace (step q2 b) with (follow q2 [b]) by reflexivity.
        eapply H2.
        rewrite Hleap.
        reflexivity.
      + assert (configuration_room_left q2 > 1).
        {
          pose proof (config_room_left_nonzero q2).
          lia.
        }
        assert (conf_state (step q2 b) = conf_state q2).
        {
          replace (step q2 b) with (follow q2 [b]) by reflexivity.
          apply state_stable.
          simpl.
          lia.
        }
        rewrite H4.
        replace (conf_state (step q1 b)) with (@inr (states a) _ false)
          by (symmetry; eauto using conf_state_step_done).
        intuition congruence.
    - erewrite !conf_state_step_done by eauto.
      tauto.
  Qed.
  Next Obligation.
    unfold Upto.closure_preserves_transition; intros.
    revert b.
    induction H0.
    - auto.
    - intros.
      replace (step (step q1 b) b0) with (follow q1 [b; b0]) by reflexivity.
      replace (step (step q2 b) b0) with (follow q2 [b; b0]) by reflexivity.
      destruct (PeanoNat.Nat.eq_dec (leap_size a q1 q2) 2);
        [|destruct (PeanoNat.Nat.eq_dec (leap_size a q1 q2) 1)].
      + eapply InterpolateBase.
        eauto.
      + assert (R (follow q1 [b]) (follow q2 [b]))
          by eauto.
        autorewrite with follow in *.
        auto.
      + autorewrite with follow.
        eapply InterpolateStep.
        * apply IHclose_interpolate.
        * assert (leap_size a q1 q2 = 1 + leap_size a (step q1 b) (step q2 b)).
          {
            eapply leap_size_step.
            pose proof (leap_size_nonzero q1 q2).
            lia.
          }
          intros.
          replace (follow (step q1 b) buf) with (follow q1 (b::buf)) by reflexivity.
          replace (follow (step q2 b) buf) with (follow q2 (b::buf)) by reflexivity.
          apply H1.
          erewrite leap_size_step; simpl; eauto.
          pose proof (leap_size_nonzero q1 q2).
          lia.
  Qed.
  Next Obligation.
    unfold Upto.closure_mono; intros.
    induction H0.
    - eauto using InterpolateBase.
    - eauto using InterpolateStep.
  Qed.

  (* Coinductively defined bisimulations with leaps are bisimulations up-to
     the interpolation closure operator. *)
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
    clear H.
    clear c1 c2.
    intros.
    constructor 2.
    - constructor 1; auto.
    - intros.
      inversion H0.
      eauto.
  Qed.

  (* Coinductively defined bisimulations are, in particular, bisimulations
     with leaps. *)
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

  (* States are bisimilar if and only if they are bisimilar with leaps. This
     makes bisimilarity with leaps a sound and complete proof principle. *)
  Theorem bisimilar_iff_bisimilar_with_leaps
          (c1 c2: conf)
    :
      BS.bisimilar c1 c2 <->
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
