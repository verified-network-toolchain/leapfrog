Require Coq.Lists.List.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.FinType.
Require Import Leapfrog.HAList.
Require Import Leapfrog.WPProofs.
Require Leapfrog.Syntax.

Open Scope list_scope.

Section Sum.
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

  Global Instance St_eq_dec: EquivDec.EqDec St eq :=
    ltac:(typeclasses eauto).

  Global Instance St_finite: @Finite St _ St_eq_dec :=
    ltac:(typeclasses eauto).

  Definition Hdr : Type := Hdr1 + Hdr2.

  Definition make_transparent {X: Type} (eq_dec: forall (x0 x1: X), {x0 = x1} + {x0 <> x1}) {l r} (opaque_eq: l = r) : l = r :=
    match eq_dec l r with
    | left transparent_eq => transparent_eq
    | _ => opaque_eq
    end.

  Definition Hdr_sz (h: Hdr) : nat :=
    match h with
    | inl h => Hdr1_sz h
    | inr h => Hdr2_sz h
    end.

  Program Definition sum : Syntax.t St Hdr_sz :=
    {| Syntax.t_states s :=
         match s with
         | inl s1 => Syntax.state_fmapSH Hdr_sz inl inl _ (a1.(Syntax.t_states) s1)
         | inr s2 => Syntax.state_fmapSH Hdr_sz inr inr _ (a2.(Syntax.t_states) s2)
         end |}.
  Next Obligation.
    destruct h; simpl.
    - apply a1.
    - apply a2.
  Qed.
  Next Obligation.
    destruct a1, a2, s;
      erewrite Syntax.state_fmapSH_size; eauto.
  Qed.

  Require Import MirrorSolve.HLists.

  Fixpoint app {A: Type} (f: A -> Type)
             {l1 l2: list A}
             (h1: HList.t f l1) 
             (h2: HList.t f l2) : HList.t f (l1 ++ l2).
    destruct l1.
    - exact h2.
    - inversion h1.
      constructor.
      + exact X.
      + apply app.
        * apply X0.
        * apply h2.
  Defined.

  Fixpoint map_inj X A (B: A -> Type) (f: X -> A)
    (l: list X) {struct l} :
      HList.t (fun x => B (f x)) l ->
      HList.t B (List.map f l).
    refine (match l as l' return HList.t (fun x => B (f x)) l' ->
                         HList.t B (List.map f l')
            with
            | [] => fun h => HList.HNil _
            | x :: xs => fun h => _
            end).
    inversion h.
    exact (HList.HCons _ X0 (map_inj _ _ _ _ _ X1)).
  Defined.
  
  Definition sum_stores
             (s1: Syntax.store Hdr1 Hdr1_sz)
             (s2: Syntax.store Hdr2 Hdr2_sz) : Syntax.store Hdr Hdr_sz :=
    app (map_inj (fun h => Syntax.v (Hdr_sz h)) inl s1)
        (map_inj (fun h => Syntax.v (Hdr_sz h)) inr s2).

  Import P4automaton.

  Require Import Coq.Program.Program.
  Inductive embed_conf1:
    P4automaton.configuration (Syntax.interp a1) ->
    P4automaton.configuration (Syntax.interp sum) ->
    Prop :=
  | EmbedConf1Inl:
    forall q
      st
      (c1: P4automaton.configuration (Syntax.interp a1))
      (c1': P4automaton.configuration (Syntax.interp sum)),
      conf_state c1 = inl q ->
      conf_state c1' = inl (inl q) ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'
  | EmbedConf1Inr:
    forall q
      st
      (c1: P4automaton.configuration (Syntax.interp a1))
      (c1': P4automaton.configuration (Syntax.interp sum)),
      conf_state c1 = inr q ->
      conf_state c1' = inr q ->
      conf_buf c1 ~= conf_buf c1' ->
      sum_stores (conf_store c1) st = conf_store c1' ->
      embed_conf1 c1 c1'.

  Inductive embed_conf2:
    P4automaton.configuration (Syntax.interp a2) ->
    P4automaton.configuration (Syntax.interp sum) ->
    Prop :=
  | EmbedConf2Inl:
    forall q
      st
      (c2: P4automaton.configuration (Syntax.interp a2))
      (c2': P4automaton.configuration (Syntax.interp sum)),
      conf_state c2 = inl q ->
      conf_state c2' = inl (inr q) ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'
  | EmbedConf2Inr:
    forall q
      st
      (c2: P4automaton.configuration (Syntax.interp a2))
      (c2': P4automaton.configuration (Syntax.interp sum)),
      conf_state c2 = inr q ->
      conf_state c2' = inr q ->
      conf_buf c2 ~= conf_buf c2' ->
      sum_stores st (conf_store c2) = conf_store c2' ->
      embed_conf2 c2 c2'.

  Inductive split_bisim (R: P4automaton.configuration (Syntax.interp sum) ->
                            P4automaton.configuration (Syntax.interp sum) ->
                            Prop)
    : P4automaton.configuration (Syntax.interp a1) ->
      P4automaton.configuration (Syntax.interp a2) ->
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

  Lemma size1 (q: St1):
    size' (Syntax.interp sum) (inl (inl q)) = size' (Syntax.interp a1) (inl q).
  Proof.
    autorewrite with size'; simpl.
    unfold Syntax.size.
    unfold sum; simpl.
    now rewrite Syntax.state_fmapSH_size.
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
    generalize (map_inj (fun h => Syntax.v (Hdr_sz h)) inr s').
    intros.
  Admitted.

  Lemma find1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) h:
    WP.P4A.find _ _ (inl h) (sum_stores s s') =
    WP.P4A.find _ _ h s.
  Proof.
    unfold WP.P4A.find.
    unfold WP.P4A.Env.get.
    unfold sum_stores.
  Admitted.

  Transparent Syntax.expr_fmapH.
  Transparent Syntax.eval_expr.

  Lemma eval_expr1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) n e:
    Syntax.eval_expr _ _ n (sum_stores s s') (Syntax.expr_fmapH _ inl (fun h : Hdr1 => sum_obligation_1 h) e) =
    Syntax.eval_expr _ _ n s e.
  Proof.
    revert s s'; dependent induction e; intros; simpl.
    - apply find1.
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
    Syntax.eval_op _ _ (sum_stores s s') (Syntax.op_fmapH _ inl (fun h => sum_obligation_1 h) o) buf1 =
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

  Opaque Syntax.op_fmapH.

  Lemma update1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St1) buf1 buf2:
    buf1 ~= buf2 ->
    Syntax.P4A.update (Syntax.interp sum)
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

  Lemma eval_sel1:
    forall s s' ty (c: Syntax.cond Hdr1_sz ty) cases default,
      Syntax.eval_sel St Hdr Hdr_sz (sum_stores s s')
                      (Syntax.cond_fmapH Hdr_sz inl (fun h => sum_obligation_1 h) c)
                      (List.map (Syntax.sel_case_fmapS inl) cases) (Syntax.state_ref_fmapS inl default) =
        match Syntax.eval_sel St1 Hdr1 Hdr1_sz s c cases default with
        | inl q' => inl (inl q')
        | inr b => inr b
        end.
  Proof.
    dependent induction cases; intros.
    - apply eq_refl.
    - simpl.
      admit.
  Admitted.

  Lemma transition1 (s: Syntax.store Hdr1 Hdr1_sz) (s': Syntax.store Hdr2 Hdr2_sz) (q: St1):
    Syntax.P4A.transitions (Syntax.interp sum) (inl q) (sum_stores s s') =
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

  Lemma embed_step1:
    forall c1 c1' b,
      embed_conf1 c1 c1' ->
      embed_conf1 (step c1 b) (step c1' b).
  Proof.
    intros.
    inversion H; subst.
    - assert (conf_buf_len c1 = conf_buf_len c1')
        by (eapply NtupleProofs.inv_jmeq_size; exact H2).
      unfold step.
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
          rewrite <- H3 in H4.
          rewrite H4.
          simpl.
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
        rewrite H1, size1 in l0.
        rewrite H0, H4 in l.
        simpl in l, l0; lia.
      + exfalso.
        rewrite H1, size1 in l0.
        rewrite H0, H4 in l.
        simpl in l, l0; lia.
      + apply EmbedConf1Inl with (q := q) (st := st); auto; simpl.
        now apply NtupleProofs.pair_proper.
    - assert (size' _ (conf_state c1) = 1) by (now rewrite H0).
      assert (size' _ (conf_state c1') = 1) by (now rewrite H1).
      unfold step.
      destruct (Compare_dec.le_lt_dec _ _),
               (Compare_dec.le_lt_dec _ _); try Lia.lia.
      destruct c1, c1'; simpl in *.
      destruct conf_state, conf_state0; try discriminate.
      autorewrite with transitions'.
      autorewrite with update'.
      now apply EmbedConf1Inr with (q := false) (st := st).
  Qed.

  Lemma embed_step2:
    forall c2 c2' b,
      embed_conf2 c2 c2' ->
      embed_conf2 (step c2 b) (step c2' b).
  Proof.
    intros.
  Admitted.

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
      P4automaton.lang_equiv_state
        (Syntax.interp sum)
        (Syntax.interp sum)
        (inl q1)
        (inr q2) ->
      P4automaton.lang_equiv_state
        (Syntax.interp a1)
        (Syntax.interp a2)
        q1
        q2.
  Proof.
    unfold P4automaton.lang_equiv_state.
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

End Sum.
