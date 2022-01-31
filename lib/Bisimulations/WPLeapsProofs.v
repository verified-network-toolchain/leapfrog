Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Import Leapfrog.WPProofs.
Require Import Leapfrog.Bisimulations.Leaps.
Require Import Leapfrog.Bisimulations.LeapsProofs.
Require Import Leapfrog.Bisimulations.AlgorithmicLeaps.
Require Import Leapfrog.Bisimulations.AlgorithmicLeapsProofs.
Require Import Leapfrog.Bisimulations.WPLeaps.
Require Import Leapfrog.Reachability.
Require Import Leapfrog.Syntax.

Ltac modus_ponens H :=
  match type of H with
  | ?P -> ?C =>
    let Hnew := fresh H in assert (Hnew: P);
    [ clear H | specialize (H Hnew); clear Hnew ]
  end.

Section WPLeapsProofs.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  Notation St := ((St1 + St2)%type).

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> nat).

  Variable (a: P4A.t St Hdr_sz).

  Variable (s1: St1).
  Variable (s2: St2).
  Definition r := reachable_states a s1 s2.

  Notation conf := (configuration (P4A.interp a)).

  Definition top q1 q2 := In (conf_to_state_template q1, conf_to_state_template q2) r.

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Lemma pre_bisimulation_embed:
    forall R T q1 q2,
      pre_bisimulation a r (WP.wp (a := a))  R T q1 q2 ->
      In (conf_to_state_template q1, conf_to_state_template q2) r ->
      AlgorithmicLeaps.pre_bisimulation
        (P4A.interp a)
        top
        (map (interp_conf_rel a) R)
        (map (interp_conf_rel a) T)
        q1 q2.
  Proof.
    intros.
    induction H.
    - now apply AlgorithmicLeaps.PreBisimulationClose.
    - apply AlgorithmicLeaps.PreBisimulationSkip.
      + intros.
        destruct H; [|contradiction].
        now apply i.
      + apply IHpre_bisimulation; eauto.
    - eapply AlgorithmicLeaps.PreBisimulationExtend.
      + intro.
        destruct H; [contradiction|].
        apply n.
        unfold interp_entailment; simpl; intros.
        auto.
      + fold (map (interp_conf_rel a) T).
        rewrite map_cons, map_app in IHpre_bisimulation.
        eauto.
      + intros.
        rewrite H2 in H4.
        eapply wp_safe; try assumption; [|apply H4].
        apply interp_rels_bound in H4.
        apply H4.
  Qed.

  Lemma not_equally_accepting_correct q1 q2:
    not_equally_accepting St1 St2 Hdr Hdr_sz a (conf_to_state_template q1,
                                            conf_to_state_template q2) = false ->
    accepting q1 <-> accepting q2.
  Proof.
    unfold not_equally_accepting, accepting; simpl; intros.
    destruct (conf_state q1), (conf_state q2);
    try destruct b; try destruct b0;
    split; intros; congruence.
  Qed.

  Lemma mk_init_accepting:
    forall (q1 q2: conf),
      ⟦mk_init _ _ _ _ _ s1 s2⟧ q1 q2 ->
      (accepting q1 <-> accepting q2).
  Proof.
    intros.
    apply not_equally_accepting_correct, Bool.not_true_iff_false; intro.
    apply interp_crel_nodup, interp_crel_quantify in H; destruct H.
    specialize (H1 (mk_rel _ _ _ _ _ (conf_to_state_template q1,
                                      conf_to_state_template q2))).
    modus_ponens H1; [ apply in_map, filter_In; intuition |].
    unfold interp_conf_rel in H1; simpl interp_store_rel in H1.
    modus_ponens H1; [ vm_compute; intuition |].
    simpl bval in H1; now specialize (H1 tt).
  Qed.

  Lemma top_closed q1 q2 bs:
    length bs = reads_left (conf_to_state_template q1,
                            conf_to_state_template q2) ->
    top q1 q2 ->
    top (follow q1 bs) (follow q2 bs).
  Proof.
    unfold top, r, reachable_states; intros.
    eapply reachable_states_closed.
    - intros; destruct H1; try contradiction; subst.
      unfold valid_state_pair, valid_state_template; simpl.
      split; apply Syntax.t_has_extract.
    - exact H0.
    - unfold reachable_step.
      apply nodup_In; simpl.
      rewrite app_nil_r, in_app_iff; left.
      unfold reachable_pair_step, reachable_pair_step'.
      apply in_prod; rewrite <- H; simpl.
      + eapply advance_correct; try typeclasses eauto; rewrite H.
        * intros; apply reads_left_upper_bound with (s := s); auto.
        * apply reads_left_lower_bound.
      + eapply advance_correct; try typeclasses eauto; rewrite H;
        setoid_rewrite reads_left_commutative.
        * intros; apply reads_left_upper_bound with (s := s); auto.
        * apply reads_left_lower_bound.
  Qed.

  Lemma wp_leaps_implies_bisim_leaps:
    forall q1 q2,
      let init := mk_init _ _ _ _ _ s1 s2 in
      pre_bisimulation a r (WP.wp (a := a)) [] init q1 q2 ->
      top q1 q2 ->
      bisimilar_with_leaps (P4A.interp a) q1 q2.
  Proof.
    intros.
    apply AlgorithmicLeapsProofs.algorithmic_leaps_implies_bisimilar_leaps
    with (R := []) (T := map (interp_conf_rel a) init) (top := top).
    - simpl interp_rels at 1.
      unfold coaccepting; intros.
      erewrite mk_init_accepting.
      + reflexivity.
      + unfold interp_crel; rewrite interp_rels_intersect_top.
        exact H1.
    - simpl interp_rels at 1.
      unfold follow_closed; intros.
      apply top_closed.
      + rewrite H1.
        unfold leap_size, reads_left; simpl.
        unfold configuration_room_left; simpl.
        destruct (conf_state q0), (conf_state q3);
        now autorewrite with size'.
      + intuition.
    - replace [] with (map (interp_conf_rel a) []) by reflexivity.
      now apply pre_bisimulation_embed.
  Qed.

End WPLeapsProofs.
