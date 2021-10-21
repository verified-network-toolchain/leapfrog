Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.WPProofs.
Require Import Poulet4.P4automata.Bisimulations.Leaps.
Require Import Poulet4.P4automata.Bisimulations.LeapsProofs.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeaps.
Require Import Poulet4.P4automata.Bisimulations.AlgorithmicLeapsProofs.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.Reachability.

Section WPLeapsProofs.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := ((S1 + S2)%type).

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Variable (s1: S1).
  Variable (s2: S2).
  Definition r := reachable_states a (length (valid_state_pairs a)) s1 s2.

  Notation conf := (configuration (P4A.interp a)).

  Definition top q1 q2 := In (conf_to_state_template q1, conf_to_state_template q2) r.

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Lemma interp_crel_app:
    forall R1 R2 q1 q2,
      interp_crel a top (R1 ++ R2) q1 q2 <->
      interp_crel a top R1 q1 q2 /\
      interp_crel a top R2 q1 q2.
  Proof.
    intros.
    induction R1; cbn; intuition.
    induction R2; intuition.
  Qed.

  Lemma pre_bisimulation_implies_interp_crel:
    forall R T q1 q2,
      pre_bisimulation a (WP.wp r) top R T q1 q2 ->
      top q1 q2 ->
      interp_crel a top (T ++ R) q1 q2.
  Proof.
    intros.
    induction H0.
    - rewrite app_nil_l.
      apply H0; simpl; auto.
    - destruct H0; [|contradiction].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
    - destruct H0; [contradiction|].
      specialize (IHpre_bisimulation H1).
      repeat rewrite interp_crel_app in *.
      rewrite interp_crel_cons in *.
      intuition.
  Qed.

  Lemma interp_rels_vs_interp_crel:
    forall q1 q2 R,
      interp_rels top (map (interp_conf_rel a) R) q1 q2 <->
      interp_crel a top R q1 q2.
  Proof.
    induction R; intuition.
  Qed.

  Lemma pre_bisimulation_embed:
    forall R T q1 q2,
      pre_bisimulation a (WP.wp r) top R T q1 q2 ->
      AlgorithmicLeaps.pre_bisimulation
        (P4A.interp a)
        top
        (map (interp_conf_rel a) R)
        (map (interp_conf_rel a) T)
        q1 q2.
  Proof.
    intros.
    induction H0.
    - apply AlgorithmicLeaps.PreBisimulationClose.
      now rewrite interp_rels_vs_interp_crel.
    - apply AlgorithmicLeaps.PreBisimulationSkip.
      + intros.
        destruct H0; [|contradiction].
        rewrite interp_rels_vs_interp_crel in H3.
        now apply i.
      + apply IHpre_bisimulation.
    - eapply AlgorithmicLeaps.PreBisimulationExtend.
      + intro.
        destruct H0; [contradiction|].
        apply n.
        unfold interp_entailment; simpl; intros.
        apply H4.
        now rewrite interp_rels_vs_interp_crel.
      + fold (map (interp_conf_rel a) T).
        rewrite map_cons, map_app in IHpre_bisimulation.
        exact IHpre_bisimulation.
      + intros.
        rewrite interp_rels_vs_interp_crel in H4.
        eapply wp_safe; auto.
        rewrite <- H2.
        exact H4.
  Admitted.

  Lemma interp_rels_intersect_top:
    forall q1 q2 R,
      interp_rels top R q1 q2 <->
      (top ⊓ interp_rels top R) q1 q2.
  Proof.
    induction R; cbn; intuition.
  Qed.

  Opaque top.

  Lemma interp_crel_quantify:
    forall R (q1 q2: conf),
      ⟦R⟧ q1 q2 <->
      top q1 q2 /\ (forall phi, In phi R -> ⦇phi⦈ q1 q2).
  Proof.
    intros; induction R.
    - intuition.
    - rewrite interp_crel_cons, IHR; intuition.
      destruct H4; subst; intuition.
  Qed.

  Transparent top.

  Lemma interp_crel_nodup:
    forall R (q1 q2: conf),
      ⟦R⟧ q1 q2 <->
      ⟦nodup (conf_rel_eq_dec (a := a)) R⟧ q1 q2.
  Proof.
    intros.
    repeat rewrite interp_crel_quantify.
    now setoid_rewrite nodup_In.
  Qed.

  Lemma init_vs_accepting:
    forall (q1 q2: conf),
      ⟦mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2⟧ q1 q2 ->
      (accepting q1 <-> accepting q2).
  Proof.
    intros.
    unfold mk_init in H0.
    rewrite <- interp_crel_nodup in H0.
    unfold mk_partition in H0.
    rewrite interp_crel_quantify in H0.
    destruct H0.
    unfold top in H0.
    unfold r in H0.
    unfold accepting.
    split; intros.
    assert (~ not_equally_accepting S1 S2 H a (conf_to_state_template q1, conf_to_state_template q2) = true).
    intro.
    assert (⦇ mk_rel S1 S2 H a (conf_to_state_template q1, conf_to_state_template q2) ⦈ q1 q2).
    apply H1.
    apply in_map.
    rewrite filter_In.
    split; auto.
    unfold mk_rel in H4.
    unfold interp_conf_rel in H4.
    vm_compute in H4.
    apply H4.
    intuition.
    exact tt.
    rewrite Bool.not_true_iff_false in H3.
    unfold not_equally_accepting in H3.
    unfold conf_to_state_template in H3.
    simpl in H3.
    rewrite H2 in H3.
    destruct (conf_state q2).
    discriminate.
    destruct b.
    reflexivity.
    discriminate.
    assert (~ not_equally_accepting S1 S2 H a (conf_to_state_template q1, conf_to_state_template q2) = true).
    intro.
    assert (⦇ mk_rel S1 S2 H a (conf_to_state_template q1, conf_to_state_template q2) ⦈ q1 q2).
    apply H1.
    apply in_map.
    rewrite filter_In.
    split; auto.
    unfold mk_rel in H4.
    unfold interp_conf_rel in H4.
    vm_compute in H4.
    apply H4.
    intuition.
    exact tt.
    rewrite Bool.not_true_iff_false in H3.
    unfold not_equally_accepting in H3.
    unfold conf_to_state_template in H3.
    simpl in H3.
    rewrite H2 in H3.
    destruct (conf_state q1).
    discriminate.
    destruct b.
    reflexivity.
    discriminate.
  Qed.

  Lemma reachable_states_closed r (p1 p2: Reachability.state_pair a):
    (forall p, List.In p r -> valid_state_pair p) ->
    List.In p1 (reachable_states' (length (valid_state_pairs a)) r) ->
    List.In p2 (reachable_step [p1]) ->
    List.In p2 (reachable_states' (length (valid_state_pairs a)) r).
  Proof.
    intros.
    apply reachable_states_bound with (fuel := Datatypes.S (length (valid_state_pairs a))); auto.
    unfold reachable_states'.
    fold (reachable_states' (length (valid_state_pairs a)) r).
    revert H2; apply reachable_step_mono.
    unfold incl; intros.
    destruct H2; try contradiction; now subst.
  Qed.

  Lemma follow_false q bs:
    conf_state q = inr false ->
    conf_state (follow (a := P4A.interp a) q bs) = inr false.
  Proof.
    revert q; induction bs; intros.
    - now autorewrite with follow.
    - autorewrite with follow.
      apply IHbs.
      unfold step.
      destruct (Compare_dec.le_lt_dec _ _).
      + simpl.
        match goal with
        | |- context [ (WP.P4A.P4A.update' _ _ ?t _) ] =>
          generalize t
        end.
        intros.
        destruct (WP.P4A.P4A.conf_state q).
        * discriminate.
        * autorewrite with update'.
          autorewrite with transitions'.
          reflexivity.
      + simpl.
        apply H0.
  Qed.

  Lemma buf_len_halted q b:
    conf_state q = inr b ->
    conf_buf_len (a := P4A.interp a) q = 0.
  Proof.
    intros.
    destruct q.
    simpl in *.
    rewrite H0 in conf_buf_sane.
    autorewrite with size' in conf_buf_sane.
    Lia.lia.
  Qed.

  Lemma foo q1 bs:
    1 <= length bs <= configuration_room_left q1 ->
    In (conf_to_state_template (follow q1 bs))
      (advance (a := a)
         (length bs)
         (conf_to_state_template q1) (st_state (conf_to_state_template q1))).
  Proof.
    intros.
    unfold advance.
    unfold conf_to_state_template at 2; simpl.
    destruct (conf_state q1) eqn:?.
    - unfold configuration_room_left in H0.
      rewrite Heqs in H0.
      autorewrite with size' in H0.
      destruct (Compare_dec.le_gt_dec _ _).
      + simpl in H0.
        assert (P4A.size (S := Reachability.S S1 S2) a s = conf_buf_len q1 + length bs) by Lia.lia.
        clear l.
        destruct H0.
        clear H2.
        revert q1 Heqs H1.
        induction bs; intros.
        * simpl in H1.
          pose proof (conf_buf_sane q1).
          rewrite Heqs in H2.
          autorewrite with size' in H2.
          simpl in H2.
          Lia.lia.
        * destruct bs.
          -- autorewrite with follow.
             simpl in H1.
             unfold step.
             destruct (Compare_dec.le_lt_dec _ _).
             ++ simpl.
                match goal with
                | |- context [ WP.P4A.P4A.update' _ _ ?t _ ] =>
                  generalize t
                end; intros.
                unfold conf_to_state_template.
                simpl.
                apply in_map_iff.
                eexists.
                split.
                reflexivity.
                destruct (WP.P4A.P4A.conf_state q1); [|discriminate].
                autorewrite with update'.
                autorewrite with transitions'.
                unfold possible_next_states.
                unfold WP.P4A.P4A.transitions.
                simpl.
                unfold P4A.transitions.
                unfold P4A.eval_trans.
                inversion Heqs.
                subst.
                destruct (P4A.st_trans _).
                apply in_eq.
                induction cases.
                simpl.
                left; reflexivity.
                simpl P4A.eval_sel.
                destruct (P4A.match_pat _ _ _ _).
                rewrite map_cons.
                apply in_cons.
                apply in_eq.
                rewrite map_cons.
                destruct IHcases.
                rewrite H2 at 2.
                apply in_eq.
                apply in_cons.
                apply in_cons.
                apply H2.
             ++ exfalso.
                rewrite Heqs in l.
                autorewrite with size' in l.
                simpl in l.
                Lia.lia.
          -- rewrite follow_equation_2.
             apply IHbs.
             ++ simpl.
                Lia.lia.
             ++ unfold step.
                destruct (Compare_dec.le_lt_dec _ _).
                ** exfalso.
                   rewrite Heqs in l.
                   autorewrite with size' in l.
                   simpl in l.
                   simpl in H1.
                   Lia.lia.
                ** now simpl.
             ++ unfold step.
                destruct (Compare_dec.le_lt_dec _ _).
                ** exfalso.
                   rewrite Heqs in l.
                   autorewrite with size' in l.
                   simpl in l.
                   simpl in H1.
                   Lia.lia.
                ** simpl in *.
                   Lia.lia.
      + clear H0; revert q1 s Heqs g; induction bs; intros.
        * autorewrite with follow.
          left.
          unfold conf_to_state_template.
          now f_equal.
        * autorewrite with follow.
          replace (conf_buf_len q1 + length (a0 :: bs))
          with ((1 + conf_buf_len q1) + length bs) by (simpl; Lia.lia).
          replace (1 + conf_buf_len q1) with (conf_buf_len (δ q1 a0)).
          apply IHbs.
          -- unfold step.
             destruct (Compare_dec.le_lt_dec _ _).
             ++ exfalso.
                rewrite Heqs in l.
                autorewrite with size' in l.
                simpl in l, g.
                Lia.lia.
             ++ now simpl.
          -- unfold step.
             destruct (Compare_dec.le_lt_dec _ _).
             ++ exfalso.
                rewrite Heqs in l.
                autorewrite with size' in l.
                simpl in l, g.
                Lia.lia.
             ++ simpl in *.
                Lia.lia.
          -- unfold step.
             destruct (Compare_dec.le_lt_dec _ _).
             ++ exfalso.
                rewrite Heqs in l.
                autorewrite with size' in l.
                simpl in l, g.
                Lia.lia.
             ++ now simpl.
    - destruct bs.
      + simpl in H0; Lia.lia.
      + autorewrite with follow.
        destruct q1.
        simpl in Heqs.
        unfold step.
        simpl.
        destruct (Compare_dec.le_lt_dec _ _).
        destruct (conf_state).
        discriminate.
        inversion Heqs.
        autorewrite with transitions'.
        left.
        unfold conf_to_state_template.
        f_equal.
        rewrite follow_false.
        reflexivity.
        simpl.
        reflexivity.
        rewrite buf_len_halted with (b := false).
        reflexivity.
        apply follow_false.
        simpl.
        reflexivity.
        right.
        rewrite Heqs in l.
        autorewrite with size' in l.
        Lia.lia.
  Qed.

  Lemma top_closed q1 q2 bs:
    length bs = reads_left (conf_to_state_template q1, conf_to_state_template q2) ->
    top q1 q2 ->
    top (follow q1 bs) (follow q2 bs).
  Proof.
    unfold top, r, reachable_states; intros.
    eapply reachable_states_closed.
    - intros.
      destruct H2; try contradiction.
      subst.
      unfold valid_state_pair, valid_state_template; simpl.
      split; apply Syntax.t_has_extract.
    - exact H1.
    - unfold reachable_step.
      apply nodup_In.
      simpl.
      rewrite app_nil_r, in_app_iff; left.
      unfold reachable_pair_step.
      unfold reachable_pair_step'.
      apply in_prod.
      + rewrite <- H0.
        simpl.
        destruct (conf_state q1) eqn:?.
        * rewrite <- Heqs.
          apply foo.
          split.
          -- rewrite H0.
             unfold reads_left; simpl.
             pose proof (conf_buf_sane q1).
             pose proof (conf_buf_sane q2).
             destruct (conf_state q1), (conf_state q2);
             autorewrite with size' in H2, H3;
             simpl in H2, H3;
             Lia.lia.
          -- unfold reads_left in H0; simpl in H0.
             unfold configuration_room_left.
             pose proof (conf_buf_sane q1).
             rewrite Heqs in *.
             autorewrite with size' in *;
             simpl in H2; simpl;
             destruct (conf_state q2);
             try Lia.lia.
        * destruct bs.
          -- unfold reads_left in H0.
             simpl in H0.
             pose proof (conf_buf_sane q1).
             pose proof (conf_buf_sane q2).
             destruct (conf_state q1), (conf_state q2);
             autorewrite with size' in *;
             simpl in H2, H3;
             Lia.lia.
          -- autorewrite with follow.
             eapply LeapsProofs.step_done in Heqs.
             unfold conf_to_state_template.
             rewrite follow_false.
             erewrite buf_len_halted.
             simpl.
             left; reflexivity.
             apply follow_false.
             exact Heqs.
             exact Heqs.
      + rewrite <- H0.
        simpl.
        destruct (conf_state q2) eqn:?.
        * rewrite <- Heqs.
          apply foo.
          split.
          -- rewrite H0.
             unfold reads_left; simpl.
             pose proof (conf_buf_sane q1).
             pose proof (conf_buf_sane q2).
             destruct (conf_state q1), (conf_state q2);
             autorewrite with size' in H2, H3;
             simpl in H2, H3;
             Lia.lia.
          -- unfold reads_left in H0; simpl in H0.
             unfold configuration_room_left.
             pose proof (conf_buf_sane q2).
             rewrite Heqs in *.
             autorewrite with size' in *;
             simpl in H2; simpl;
             destruct (conf_state q1);
             try Lia.lia.
        * destruct bs.
          -- unfold reads_left in H0.
             simpl in H0.
             pose proof (conf_buf_sane q1).
             pose proof (conf_buf_sane q2).
             destruct (conf_state q1), (conf_state q2);
             autorewrite with size' in *;
             simpl in H2, H3;
             Lia.lia.
          -- autorewrite with follow.
             eapply LeapsProofs.step_done in Heqs.
             unfold conf_to_state_template.
             rewrite follow_false.
             erewrite buf_len_halted.
             simpl.
             left; reflexivity.
             apply follow_false.
             exact Heqs.
             exact Heqs.
  Qed.

  Lemma wp_leaps_implies_bisim_leaps:
    forall q1 q2,
      let init := mk_init _ _ _ _ (length (valid_state_pairs a)) s1 s2 in
      pre_bisimulation a (WP.wp r) top [] init q1 q2 ->
      top q1 q2 ->
      bisimilar_with_leaps (P4A.interp a) q1 q2.
  Proof.
    intros.
    apply AlgorithmicLeapsProofs.algorithmic_leaps_implies_bisimilar_leaps
    with (R := []) (T := map (interp_conf_rel a) init) (top := top).
    - simpl interp_rels at 1.
      unfold coaccepting; intros.
      erewrite init_vs_accepting.
      + reflexivity.
      + rewrite <- interp_rels_vs_interp_crel, interp_rels_intersect_top.
        exact H2.
    - simpl interp_rels at 1.
      unfold follow_closed; intros.
      apply top_closed.
      rewrite H2.
      unfold leap_size, reads_left.
      simpl.
      unfold configuration_room_left.
      simpl.
      unfold Reachability.S.
      destruct (conf_state q0), (conf_state q3);
      now autorewrite with size'.
      intuition.
    - replace [] with (map (interp_conf_rel a) []) by reflexivity.
      now apply pre_bisimulation_embed.
  Qed.

End WPLeapsProofs.
