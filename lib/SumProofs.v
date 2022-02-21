Require Import Coq.micromega.Lia.
Require Import Coq.Program.Program.
Require Import Coq.Classes.EquivDec.
Require Coq.Logic.Eqdep_dec.
Require Coq.Lists.List.

Require Import Leapfrog.FinType.
Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.HAList.
Require Import Leapfrog.WPProofs.
Require Import Leapfrog.Sum.
Require Import Leapfrog.P4automaton.
Require Leapfrog.Syntax.

Require Import MirrorSolve.HLists.

Open Scope list_scope.

Section SumProofs.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr1: Type).
  Variable (Hdr1_sz : Hdr1 -> nat).
  Context `{Hdr1_eq_dec: EquivDec.EqDec Hdr1 eq}.
  Context `{Hdr1_finite: @Finite Hdr1 _ Hdr1_eq_dec}.

  Variable (Hdr2: Type).
  Variable (Hdr2_sz : Hdr2 -> nat).
  Context `{Hdr2_eq_dec: EquivDec.EqDec Hdr2 eq}.
  Context `{Hdr2_finite: @Finite Hdr2 _ Hdr2_eq_dec}.

  Variable (a1: Syntax.t St1 Hdr1_sz).
  Variable (a2: Syntax.t St2 Hdr2_sz).

  Notation St := (St1 + St2)%type.

  Lemma find1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) h:
    Syntax.find _ _ (inl h) (sum_stores s s') =
    Syntax.find _ _ h s.
  Proof.
    unfold Syntax.find.
    unfold Syntax.Env.get.
    unfold sum_stores.
    set (t1 := (HList.map_inj (fun h0 : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h0)) inl s)).
    set (l1 := List.map (@inl _ Hdr2) (enum Hdr1)) in *.
    assert (pf: List.In (inl h) l1).
    {
      unfold l1.
      rewrite List.in_map_iff.
      eexists.
      split; eauto.
      apply elem_of_enum.
    }
    eapply eq_trans.
    eapply HList.get_app_l with (t1 := t1) (pf' := pf); auto.
    unfold t1.
    erewrite HList.get_map_inj; eauto.
    intros.
    congruence.
  Qed.

  Lemma find2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) h:
    Syntax.find _ _ (inr h) (sum_stores s s') =
    Syntax.find _ _ h s'.
  Proof.
    unfold Syntax.find.
    unfold Syntax.Env.get.
    unfold sum_stores.
    set (t2 := (HList.map_inj (fun h0 : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h0)) inr s')).
    set (l2 := List.map (@inr Hdr1 _) (enum Hdr2)) in *.
    assert (pf: List.In (inr h) l2).
    {
      unfold l2.
      rewrite List.in_map_iff.
      eexists.
      split; eauto.
      apply elem_of_enum.
    }
    eapply eq_trans.
    eapply HList.get_app_r with (t2 := t2) (pf' := pf);
      rewrite List.in_map_iff; firstorder congruence.
    unfold t2.
    erewrite HList.get_map_inj; eauto.
    intros.
    congruence.
  Qed.

  Lemma assign1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) hdr v1 v2:
    v1 = v2 ->
    Syntax.assign _ _ (inl hdr) v1 (sum_stores s s') =
    sum_stores (Syntax.assign _ _ hdr v2 s) s'.
  Proof.
    intros; subst v1.
    unfold Syntax.store in *.
    simpl in *.
    unfold sum_stores.
    unfold Syntax.assign, Syntax.Env.bind.
    pose proof (HList.bind_app_l _ (HList.map_inj (fun h : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h)) inl s)
                                   (HList.map_inj (fun h : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h)) inr s')).
    erewrite H.
    f_equal.
    erewrite HList.bind_map_inj with (pf' := elem_of_enum hdr) by (intros; congruence).
    reflexivity.
    Unshelve.
    pose proof (@elem_of_enum Hdr1 _ _ _ hdr).
    apply List.in_map_iff.
    eexists.
    intuition eauto.
  Qed.

  Lemma assign2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) hdr v1 v2:
    v1 = v2 ->
    Syntax.assign _ _ (inr hdr) v1 (sum_stores s s') =
    sum_stores s (Syntax.assign _ _ hdr v2 s').
  Proof.
    intros; subst v1.
    unfold Syntax.store in *.
    simpl in *.
    unfold sum_stores.
    unfold Syntax.assign, Syntax.Env.bind.
    pose proof (HList.bind_app_r _ (HList.map_inj (fun h : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h)) inl s)
                                   (HList.map_inj (fun h : Hdr Hdr1 Hdr2 => Syntax.v (Hdr_sz Hdr1_sz Hdr2_sz h)) inr s')).
    erewrite H
      by (rewrite List.in_map_iff; firstorder congruence).
    f_equal.
    erewrite HList.bind_map_inj with (pf' := elem_of_enum hdr); eauto.
    intros; congruence.
    Unshelve.
    pose proof (@elem_of_enum Hdr2 _ _ _ hdr).
    apply List.in_map_iff.
    eexists.
    intuition eauto.
  Qed.

  Lemma size1 (q: St1):
    Syntax.P4A.size' (Syntax.interp (sum a1 a2)) (inl (inl q)) = size' (Syntax.interp a1) (inl q).
  Proof.
    autorewrite with size'; simpl.
    unfold Syntax.size.
    unfold sum; simpl.
    now rewrite Syntax.state_fmapSH_size.
  Qed.

  Lemma size2 (q: St2):
    size' (Syntax.interp (sum a1 a2)) (inl (inr q)) = size' (Syntax.interp a2) (inl q).
  Proof.
    autorewrite with size'; simpl.
    unfold Syntax.size.
    unfold sum; simpl.
    now rewrite Syntax.state_fmapSH_size.
  Qed.

  Transparent Syntax.expr_fmapH.
  Transparent Syntax.eval_expr.

  Lemma eval_expr1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) n e:
    Syntax.eval_expr _ _ n (sum_stores s s') (Syntax.expr_fmapH _ inl (fun _ => eq_refl) e) =
    Syntax.eval_expr _ _ n s e.
  Proof.
    revert s s'; dependent induction e; intros; simpl.
    - apply find1.
    - reflexivity.
    - now rewrite IHe.
    - now rewrite IHe1, IHe2.
  Qed.

  Lemma eval_expr2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) n e:
    Syntax.eval_expr _ _ n (sum_stores s s') (Syntax.expr_fmapH _ inr (fun _ => eq_refl) e) =
    Syntax.eval_expr _ _ n s' e.
  Proof.
    revert s s'; dependent induction e; intros; simpl.
    - apply find2.
    - reflexivity.
    - now rewrite IHe.
    - now rewrite IHe1, IHe2.
  Qed.

  Opaque Syntax.expr_fmapH.
  Opaque Syntax.eval_expr.

  Transparent Syntax.op_fmapH.
  Transparent Syntax.eval_op.

  Lemma eval_op1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) o buf1 buf2:
    buf1 ~= buf2 ->
    Syntax.eval_op _ _ (sum_stores s s') (Syntax.op_fmapH _ inl (fun _ => eq_refl) o) buf1 =
    sum_stores (Syntax.eval_op _ _ s o buf2) s'.
  Proof.
    revert s s'; dependent induction o; intros; simpl.
    - reflexivity.
    - erewrite IHo1; auto.
      erewrite IHo2; auto.
      + repeat rewrite Ntuple.rewrite_size_jmeq.
        apply NtupleProofs.t2l_eq.
        repeat rewrite Ntuple.t2l_n_tuple_skip_n.
        f_equal.
        * apply Syntax.op_fmapH_size.
        * now apply NtupleProofs.eq_t2l.
      + repeat rewrite Ntuple.rewrite_size_jmeq.
        apply NtupleProofs.t2l_eq.
        repeat rewrite Ntuple.t2l_n_tuple_take_n.
        f_equal.
        * apply Syntax.op_fmapH_size.
        * now apply NtupleProofs.eq_t2l.
    - erewrite assign1; auto.
      f_equal.
      apply JMeq_eq; auto.
    - erewrite assign1; auto.
      apply eval_expr1.
  Qed.

  Lemma eval_op2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) o buf1 buf2:
    buf1 ~= buf2 ->
    Syntax.eval_op _ _ (sum_stores s s') (Syntax.op_fmapH _ inr (fun _ => eq_refl) o) buf1 =
    sum_stores s (Syntax.eval_op _ _ s' o buf2).
  Proof.
    revert s s'; dependent induction o; intros; simpl.
    - reflexivity.
    - erewrite IHo1, IHo2; auto.
      + repeat rewrite Ntuple.rewrite_size_jmeq.
        apply NtupleProofs.t2l_eq.
        repeat rewrite Ntuple.t2l_n_tuple_skip_n.
        f_equal.
        * apply Syntax.op_fmapH_size.
        * now apply NtupleProofs.eq_t2l.
      + repeat rewrite Ntuple.rewrite_size_jmeq.
        apply NtupleProofs.t2l_eq.
        repeat rewrite Ntuple.t2l_n_tuple_take_n.
        f_equal.
        * apply Syntax.op_fmapH_size.
        * now apply NtupleProofs.eq_t2l.
    - erewrite assign2; auto.
      f_equal.
      apply JMeq_eq; auto.
    - erewrite assign2; auto.
      apply eval_expr2.
  Qed.

  Opaque Syntax.eval_op.
  Opaque Syntax.op_fmapH.

  Lemma update1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St1) buf1 buf2:
    buf1 ~= buf2 ->
    Syntax.P4A.update (Syntax.interp (sum a1 a2))
                      (inl q)
                      buf1
                      (sum_stores s s') =
    sum_stores (Syntax.P4A.update (Syntax.interp a1) q buf2 s) s'
  .
  Proof.
    intros.
    unfold Syntax.P4A.update; simpl.
    unfold Syntax.update; simpl.
    erewrite eval_op1; auto.
    repeat f_equal.
    now repeat rewrite NtupleProofs.eq_rect_jmeq.
  Qed.

  Lemma update2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St2) buf1 buf2:
    buf1 ~= buf2 ->
    Syntax.P4A.update (Syntax.interp (sum a1 a2))
                      (inr q)
                      buf1
                      (sum_stores s s') =
    sum_stores s (Syntax.P4A.update (Syntax.interp a2) q buf2 s')
  .
  Proof.
    intros.
    unfold Syntax.P4A.update; simpl.
    unfold Syntax.update; simpl.
    erewrite eval_op2; auto.
    repeat f_equal.
    now repeat rewrite NtupleProofs.eq_rect_jmeq.
  Qed.

  Lemma eval_sel1:
    forall s s' ty (c: Syntax.cond Hdr1_sz ty) cases default,
      Syntax.eval_sel St (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
                      (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inl (fun _ => eq_refl) c)
                      (List.map (Syntax.sel_case_fmapS inl) cases) (Syntax.state_ref_fmapS inl default) =
        match Syntax.eval_sel St1 Hdr1 Hdr1_sz s c cases default with
        | inl q' => inl (inl q')
        | inr b => inr b
        end.
  Proof.
    dependent induction cases; intros.
    - apply eq_refl.
    - simpl.
      rewrite IHcases.
      assert (
      Syntax.match_pat Hdr1 Hdr1_sz s c (Syntax.sc_pat a)
                       =
      Syntax.match_pat (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
        (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inl (fun _ => eq_refl) c)
        (Syntax.sc_pat a)).
      {
        set (P ty (pat: Syntax.pat ty) cond :=
               Syntax.match_pat Hdr1 Hdr1_sz s cond pat
               =
                 Syntax.match_pat (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
                                  (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inl (fun _ => eq_refl) cond)
                                  pat).
        cut (P _ (Syntax.sc_pat a) c); simpl; auto.
        generalize (Syntax.sc_pat a).
        generalize c.
        generalize ty.
        eapply pat_cond_ind; intros; unfold P in *.
        - unfold Syntax.cond_fmapH;
          autorewrite with match_pat.
          erewrite eval_expr1.
          auto.
        - auto.
        - autorewrite with match_pat.
          rewrite H, H0.
          auto.
      }
      simpl in *; rewrite <- H.
      destruct (Syntax.match_pat Hdr1 Hdr1_sz s c (Syntax.sc_pat a)); eauto.
  Qed.

  Lemma eval_sel2:
    forall s s' ty (c: Syntax.cond Hdr2_sz ty) cases default,
      Syntax.eval_sel St (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
                      (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inr (fun _ => eq_refl) c)
                      (List.map (Syntax.sel_case_fmapS inr) cases) (Syntax.state_ref_fmapS inr default) =
        match Syntax.eval_sel St2 Hdr2 Hdr2_sz s' c cases default with
        | inl q' => inl (inr q')
        | inr b => inr b
        end.
  Proof.
    dependent induction cases; intros.
    - apply eq_refl.
    - simpl.
      rewrite IHcases.
      assert (
      Syntax.match_pat Hdr2 Hdr2_sz s' c (Syntax.sc_pat a)
                       =
      Syntax.match_pat (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
        (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inr (fun _ => eq_refl) c)
        (Syntax.sc_pat a)).
      {
        set (P ty (pat: Syntax.pat ty) cond :=
               Syntax.match_pat Hdr2 Hdr2_sz s' cond pat
               =
                 Syntax.match_pat (Hdr Hdr1 Hdr2) (Hdr_sz Hdr1_sz Hdr2_sz) (sum_stores s s')
                                  (Syntax.cond_fmapH (Hdr_sz Hdr1_sz Hdr2_sz) inr (fun _ => eq_refl) cond)
                                  pat).
        cut (P _ (Syntax.sc_pat a) c); simpl; auto.
        generalize (Syntax.sc_pat a).
        generalize c.
        generalize ty.
        eapply pat_cond_ind; intros; unfold P in *.
        - unfold Syntax.cond_fmapH;
          autorewrite with match_pat.
          erewrite eval_expr2.
          auto.
        - auto.
        - autorewrite with match_pat.
          rewrite H, H0.
          auto.
      }
      simpl in *; rewrite <- H.
      destruct (Syntax.match_pat _ _ _ _ _); eauto.
  Qed.

  Lemma transition1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St1):
    Syntax.P4A.transitions (Syntax.interp (sum a1 a2)) (inl q) (sum_stores s s') =
    match Syntax.P4A.transitions (Syntax.interp a1) q s with
    | inl q' => inl (inl q')
    | inr b => inr b
    end.
  Proof.
    simpl.
    unfold Syntax.transitions, Syntax.eval_trans.
    simpl in *.
    destruct (Syntax.st_trans (Syntax.t_states a1 q)); simpl.
    - unfold Syntax.state_ref_fmapS.
      reflexivity.
    - apply eval_sel1.
  Qed.

  Lemma transition2 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St2):
    Syntax.P4A.transitions (Syntax.interp (sum a1 a2)) (inr q) (sum_stores s s') =
    match Syntax.P4A.transitions (Syntax.interp a2) q s' with
    | inl q' => inl (inr q')
    | inr b => inr b
    end.
  Proof.
    simpl.
    unfold Syntax.transitions, Syntax.eval_trans.
    simpl in *.
    destruct (Syntax.st_trans (Syntax.t_states a2 q)); simpl.
    - unfold Syntax.state_ref_fmapS.
      reflexivity.
    - apply eval_sel2.
  Qed.

  Inductive embed_conf1:
    configuration (Syntax.interp a1) ->
    configuration (Syntax.interp (sum a1 a2)) ->
    Prop :=
  | EmbedConf1Inl:
    forall q
      st
      (c1: configuration (Syntax.interp a1))
      (c1': configuration (Syntax.interp (sum a1 a2))),
      conf_state c1 = inl q ->
      conf_state c1' = inl (inl q) ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'
  | EmbedConf1Inr:
    forall q
      st
      (c1: configuration (Syntax.interp a1))
      (c1': configuration (Syntax.interp (sum a1 a2))),
      conf_state c1 = inr q ->
      conf_state c1' = inr q ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'.

  Inductive embed_conf2:
    configuration (Syntax.interp a2) ->
    configuration (Syntax.interp (sum a1 a2)) ->
    Prop :=
  | EmbedConf2Inl:
    forall q
      st
      (c2: configuration (Syntax.interp a2))
      (c2': configuration (Syntax.interp (sum a1 a2))),
      conf_state c2 = inl q ->
      conf_state c2' = inl (inr q) ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'
  | EmbedConf2Inr:
    forall q
      st
      (c2: configuration (Syntax.interp a2))
      (c2': configuration (Syntax.interp (sum a1 a2))),
      conf_state c2 = inr q ->
      conf_state c2' = inr q ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'.

  Inductive split_bisim (R: configuration (Syntax.interp (sum a1 a2)) ->
                            configuration (Syntax.interp (sum a1 a2)) ->
                            Prop)
    : configuration (Syntax.interp a1) ->
      configuration (Syntax.interp a2) ->
      Prop :=
  | MkBisim: forall c1 c2 c1' c2',
      embed_conf1 c1 c1' ->
      embed_conf2 c2 c2' ->
      R c1' c2' ->
      split_bisim R c1 c2.

  Lemma embed_accepting1:
    forall c1 c1',
      embed_conf1 c1 c1' ->
      accepting c1 <-> accepting c1'.
  Proof.
    unfold accepting.
    destruct c1, c1'.
    split; intros.
    - inversion H; subst; simpl in *; congruence.
    - inversion H; subst; simpl in *; congruence.
  Qed.

  Lemma embed_accepting2:
    forall c2 c2',
      embed_conf2 c2 c2' ->
      accepting c2 <-> accepting c2'.
  Proof.
    unfold accepting.
    destruct c2, c2'.
    split; intros.
    - inversion H; subst; simpl in *; congruence.
    - inversion H; subst; simpl in *; congruence.
  Qed.

  Lemma embed_step1:
    forall c1 c1' b,
      embed_conf1 c1 c1' ->
      embed_conf1 (step c1 b) (step c1' b).
  Proof.
    intros.
    inversion H; subst;
    assert (conf_buf_len c1 = conf_buf_len c1')
      by (eapply NtupleProofs.inv_jmeq_size; exact H2).
    - unfold step.
      destruct (Compare_dec.le_lt_dec _ _),
               (Compare_dec.le_lt_dec _ _); try lia.
      + destruct c1, c1'; simpl in *.
        destruct conf_state, conf_state0; try discriminate.
        autorewrite with transitions'.
        autorewrite with update'.
        inversion H0; inversion H1; subst.
        erewrite update1.
        * match goal with
          | |- context[Syntax.P4A.transitions _ q ?c] =>
            set (conf_store_new := c)
          end.
          match goal with
          | |- context[Syntax.P4A.transitions _ (inl q) ?c] =>
            set (conf_store_new' := c)
          end.
          assert (conf_store_new' = sum_stores conf_store_new st)
            by (subst conf_store_new'; reflexivity).
          pose proof (transition1 conf_store_new st q).
          rewrite <- H3 in H4; simpl in *.
          destruct (Syntax.transitions St1 Hdr1 Hdr1_sz a1 q conf_store_new).
          -- eapply EmbedConf1Inl; simpl; now subst.
          -- eapply EmbedConf1Inr; simpl; now subst.
        * rewrite H2.
          erewrite <- Ntuple.rewrite_size_jmeq; symmetry.
          erewrite <- Ntuple.rewrite_size_jmeq; symmetry.
          unfold Ntuple.rewrite_size.
          repeat rewrite rew_opp_l.
          now apply NtupleProofs.pair_proper.
      + exfalso.
        replace (conf_state c1')
          with (inl (B := bool) (inl (B := St2) q))
          in l0 by now f_equal.
        rewrite size1 in l0.
        rewrite H0, H4 in l.
        eapply PeanoNat.Nat.lt_irrefl.
        eapply PeanoNat.Nat.le_lt_trans.
        * apply l.
        * apply l0.
      + exfalso.
        replace (conf_state c1')
          with (inl (B := bool) (inl (B := St2) q))
          in l0 by now f_equal.
        rewrite size1 in l0.
        rewrite H0, H4 in l.
        eapply PeanoNat.Nat.lt_irrefl.
        eapply PeanoNat.Nat.lt_le_trans.
        * apply l.
        * apply l0.
      + apply EmbedConf1Inl with (q := q) (st := st); auto; simpl.
        now apply NtupleProofs.pair_proper.
    - unfold step.
      destruct (Compare_dec.le_lt_dec _ _),
               (Compare_dec.le_lt_dec _ _).
      + destruct c1, c1'; simpl in *.
        destruct conf_state, conf_state0; try discriminate.
        autorewrite with transitions'.
        autorewrite with update'.
        now apply EmbedConf1Inr with (q := false) (st := st).
      + exfalso.
        replace (conf_state c1')
          with (inr (A := St) q)
          in l0 by now f_equal.
        autorewrite with size' in l0.
        lia.
      + exfalso.
        replace (conf_state c1)
          with (inr (A := St1) q)
          in l by now f_equal.
        autorewrite with size' in l.
        lia.
      + exfalso.
        replace (conf_state c1)
          with (inr (A := St1) q)
          in l by now f_equal.
        autorewrite with size' in l.
        lia.
  Qed.

  Lemma embed_step2:
    forall c2 c2' b,
      embed_conf2 c2 c2' ->
      embed_conf2 (step c2 b) (step c2' b).
  Proof.
    intros.
    inversion H; subst.
    - assert (conf_buf_len c2 = conf_buf_len c2')
        by (eapply NtupleProofs.inv_jmeq_size; exact H2).
      unfold step.
      destruct (Compare_dec.le_lt_dec _ _),
               (Compare_dec.le_lt_dec _ _); try lia.
      + destruct c2, c2'; simpl in *.
        destruct conf_state, conf_state0; try discriminate.
        autorewrite with transitions'.
        autorewrite with update'.
        inversion H0; inversion H1; subst.
        erewrite update2.
        * match goal with
          | |- context[Syntax.P4A.transitions _ q ?c] =>
            set (conf_store_new := c)
          end.
          match goal with
          | |- context[Syntax.P4A.transitions _ (inr q) ?c] =>
            set (conf_store_new' := c)
          end.
          assert (conf_store_new' = sum_stores st conf_store_new)
            by (subst conf_store_new'; reflexivity).
          pose proof (transition2 st conf_store_new q).
          rewrite <- H3 in H4; simpl in *.
          destruct (Syntax.transitions _ _ _ a2 q conf_store_new).
          -- eapply EmbedConf2Inl; simpl; now subst.
          -- eapply EmbedConf2Inr; simpl; now subst.
        * rewrite H2.
          erewrite <- Ntuple.rewrite_size_jmeq; symmetry.
          erewrite <- Ntuple.rewrite_size_jmeq; symmetry.
          unfold Ntuple.rewrite_size.
          repeat rewrite rew_opp_l.
          now apply NtupleProofs.pair_proper.
      + exfalso.
        replace (conf_state c2')
          with (inl (B := bool) (inr (A := St1) q))
          in l0 by now f_equal.
        rewrite size2 in l0.
        rewrite H0, H4 in l.
        eapply PeanoNat.Nat.lt_irrefl.
        eapply PeanoNat.Nat.le_lt_trans.
        * apply l.
        * apply l0.
      + exfalso.
        replace (conf_state c2')
          with (inl (B := bool) (inr (A := St1) q))
          in l0 by now f_equal.
        rewrite size2 in l0.
        rewrite H0, H4 in l.
        eapply PeanoNat.Nat.lt_irrefl.
        eapply PeanoNat.Nat.lt_le_trans.
        * apply l.
        * apply l0.
      + apply EmbedConf2Inl with (q := q) (st := st); auto; simpl.
        now apply NtupleProofs.pair_proper.
    - unfold step.
      destruct (Compare_dec.le_lt_dec _ _),
               (Compare_dec.le_lt_dec _ _).
      + destruct c2, c2'; simpl in *.
        destruct conf_state, conf_state0; try discriminate.
        autorewrite with transitions'.
        autorewrite with update'.
        now apply EmbedConf2Inr with (q := false) (st := st).
      + exfalso.
        replace (conf_state c2')
          with (inr (A := St) q)
          in l0 by now f_equal.
        autorewrite with size' in l0.
        lia.
      + exfalso.
        replace (conf_state c2)
          with (inr (A := St2) q)
          in l by now f_equal.
        autorewrite with size' in l.
        lia.
      + exfalso.
        replace (conf_state c2)
          with (inr (A := St2) q)
          in l by now f_equal.
        autorewrite with size' in l.
        lia.
  Qed.

  Lemma split_is_bisim:
    forall R,
      bisimulation R ->
      bisimulation (split_bisim R).
  Proof.
    unfold bisimulation; intros.
    inversion H0; subst.
    apply H in H3; destruct H3.
    split.
    - erewrite embed_accepting1 by eauto.
      erewrite embed_accepting2 by eauto.
      auto.
    - intros.
      econstructor.
      + apply embed_step1, H1.
      + apply embed_step2, H2.
      + apply H4.
  Qed.

  Lemma sum_thing:
    forall (q1: St1) (q2: St2),
      lang_equiv_state
        (Syntax.interp (sum a1 a2))
        (Syntax.interp (sum a1 a2))
        (inl q1)
        (inr q2) ->
      lang_equiv_state
        (Syntax.interp a1)
        (Syntax.interp a2)
        q1
        q2.
  Proof.
    unfold lang_equiv_state.
    intros.
    apply bisimilar_iff_lang_equiv.
    setoid_rewrite bisimilar_iff_lang_equiv in H.
    unfold bisimilar.
    simpl in s1, s2.
    pose (sum_stores s1 s2) as s0.
    specialize (H s0 s0).
    destruct H as [R [Hbisim Hrel]].
    exists (split_bisim R).
    split.
    - auto using split_is_bisim.
    - econstructor; eauto.
      + econstructor; simpl; eauto.
        unfold s0.
        reflexivity.
      + econstructor; simpl; eauto.
        unfold s0.
        reflexivity.
  Qed.

End SumProofs.
