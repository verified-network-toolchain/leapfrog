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

  Lemma step_done:
    forall (q: conf) s b,
      conf_state q = inr s ->
      conf_state (step q b) = inr s.
  Proof.
    intros.
    unfold step.
    destruct (le_lt_dec _ _).
    - cbn.
      generalize (eq_rect (S (conf_buf_len q)) (Ntuple.n_tuple bool)
                          (Ntuple.n_tuple_cons (conf_buf q) b) (size' a (conf_state q)) 
                          (squeeze (conf_buf_sane _) l)).
      rewrite H.
      intros.
      autorewrite with transitions'.
      reflexivity.
    - simpl.
      rewrite H in l.
      autorewrite with size' in *.
      lia.
  Qed.

  Program Instance close_interpolate_sound
    : Upto.SoundClosure a (close_interpolate a).
  Next Obligation.
    eauto using InterpolateBase.
  Qed.
  Next Obligation.
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
          by (symmetry; eauto using step_done).
        intuition congruence.
    - erewrite !step_done by eauto.
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
          by (symmetry; eauto using step_done).
        intuition congruence.
    - erewrite !step_done by eauto.
      tauto.
  Qed.
  Next Obligation.
    revert b.
    induction H0.
    - intros.
      destruct q1 as [sr1 l1 buf1 Hsane1 store1].
      destruct q2 as [sr2 l2 buf2 Hsane2 store2].
      destruct sr1 as [s1|s1] eqn:Hs1,
               sr2 as [s2|s2] eqn:Hs2.
      + admit.
      + admit.
      + admit.
      + eapply InterpolateStep.
        cbv.
        simpl in *.
        subst.
  Admitted.
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
    clear H.
    clear c1 c2.
    intros.
    constructor 2.
    - constructor 1; auto.
    - intros.
      inversion H0.
      eauto.
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
