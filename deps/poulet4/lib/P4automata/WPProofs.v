Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.JMeq.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Ntuple.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.WP.

Section WPProofs.
  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Definition S: Type := S1 + S2.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).
  Notation conf := (configuration (P4A.interp a)).
  
  Lemma skipn_skipn:
    forall A (x: list A) n m,
      skipn n (skipn m x) = skipn (n + m) x.
  Proof.
    induction x; intros.
    - rewrite !skipn_nil.
      reflexivity.
    - destruct m.
      + simpl.
        rewrite <- plus_n_O.
        reflexivity.
      + rewrite <- plus_n_Sm.
        simpl.
        apply IHx.
  Qed.

  Lemma firstn_firstn:
    forall A (x: list A) n m,
      firstn n (firstn m x) = firstn (min n m) x.
  Proof.
    induction x; intros.
    - rewrite !firstn_nil.
      reflexivity.
    - destruct m.
      + rewrite Min.min_0_r.
        rewrite firstn_nil.
        reflexivity.
      + simpl.
        destruct n; [reflexivity|].
        simpl.
        rewrite IHx.
        reflexivity.
  Qed.

  Lemma slice_slice:
    forall A (x: list A) hi lo hi' lo',
      P4A.slice (P4A.slice x hi lo) hi' lo' =
      P4A.slice x (Nat.min (lo + hi') hi) (lo + lo').
  Proof.
    intros.
    unfold P4A.slice.
    rewrite firstn_skipn_comm.
    rewrite skipn_skipn.
    rewrite PeanoNat.Nat.add_comm.
    rewrite firstn_firstn.
    replace (Nat.min (lo + (1 + hi')) (1 + hi))
      with (1 + Nat.min (lo + hi') hi)
      by Lia.lia.
    reflexivity.
  Qed.

  Lemma beslice_interp_length:
    forall b1 b2 ctx e hi lo,
      @be_size H ctx b1 b2 (BESlice e hi lo) =
      @be_size H ctx b1 b2 (beslice e hi lo).
  Proof.
    intros.
    unfold beslice.
    destruct e; eauto.
    - unfold be_size.
      rewrite P4A.slice_len.
      Lia.lia.
    - unfold be_size.
      fold (be_size b1 b2 e).
      Lia.lia.
  Qed.

  Lemma skipn_n_tuple_skip_n_eq:
    forall A (l: list A) n,
      JMeq (Ntuple.l2t (skipn n l)) (Ntuple.n_tuple_skip_n n (Ntuple.l2t l)).
  Proof.
    unfold Ntuple.n_tuple_skip_n.
    intros.
    revert l.
    induction n; intros.
    - simpl (skipn 0 _).
      rewrite Ntuple.rewrite_size_jmeq.
      rewrite Ntuple.l2t_t2l.
      reflexivity.
    - rewrite !Ntuple.rewrite_size_jmeq.
      rewrite Ntuple.t2l_l2t.
      reflexivity.
  Qed.

  Lemma slice_n_tuple_slice_eq:
    forall A (l: list A) hi lo,
      JMeq (l2t (ConfRel.P4A.slice l hi lo)) (Ntuple.n_tuple_slice hi lo (l2t l)).
  Proof.
    intros.
    unfold Ntuple.n_tuple_slice.
    unfold ConfRel.P4A.slice.
    rewrite skipn_n_tuple_skip_n_eq.
    (* need lemma about take_n/firstn *)
  Admitted.

  Lemma beslice_interp:
    forall ctx (e: bit_expr H ctx) hi lo valu (q1 q2: conf),
      JMeq
        (interp_bit_expr (beslice e hi lo) valu q1 q2)
        (interp_bit_expr (BESlice e hi lo) valu q1 q2).
  Proof.
    induction e; intros;
      repeat (progress cbn
              || autorewrite with interp_bit_expr
              || rewrite rewrite_size_eq);
      eauto.
    - apply slice_n_tuple_slice_eq.
    - admit.
  Admitted.

  Lemma beconcat_interp:
    forall ctx (e1 e2: bit_expr H ctx) valu (q1 q2: conf),
      JMeq (interp_bit_expr (beconcat e1 e2) valu q1 q2)
           (interp_bit_expr (BEConcat e1 e2) valu q1 q2).
  Proof.
    induction e1; destruct e2; intros; simpl; auto.
    autorewrite with interp_bit_expr.
    eauto using l2t_app.
  Qed.

  (*
  Lemma be_subst_hdr_left:
    forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) s1 st1 buf1 c2 (w: Ntuple.n_tuple bool size) v,
        interp_bit_expr exp valu q c2 = v ->
        conf_state q = s1 ->
        conf_store q = st1 ->
        conf_buf q = buf1 ->
        v = Ntuple.t2l w ->
        interp_bit_expr (a:=a) phi valu
                        (update_conf_store (a:=P4A.interp a)
                                           (P4A.assign _ hdr (P4A.VBits size w) st1)
                                           q)
                        c2 =
        interp_bit_expr (WP.be_subst phi exp (BEHdr c Left (P4A.HRVar (existT _ _ hdr))))
                        valu
                        q
                        c2.
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); simpl; congruence.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        simpl.
        rewrite P4A.eq_dec_refl.
        simpl.
        rewrite P4A.eq_dec_refl.
        congruence.
      + simpl.
        destruct h.
        dependent destruction var.
        simpl in *.
        unfold P4A.find, P4A.assign.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
               | |- _ => progress unfold "===" in *
               | |- _ => progress simpl in *
               | |- _ => progress subst
               end;
          congruence.
    - reflexivity.
    - simpl.
      subst.
      erewrite IHphi; eauto.
      rewrite beslice_interp.
      reflexivity.
    - simpl.
      rewrite beconcat_interp.
      erewrite IHphi1, IHphi2; eauto.
  Qed.
  Lemma be_subst_hdr_right:
    forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) s2 st2 buf2 c1 (w: Ntuple.n_tuple bool size) v,
        interp_bit_expr exp valu c1 q = v ->
        conf_state q = s2 ->
        conf_store q = st2 ->
        conf_buf q = buf2 ->
        v = Ntuple.t2l w ->
        interp_bit_expr (a:=a) phi valu
                        c1
                        (update_conf_store (a:=P4A.interp a)
                                           (P4A.assign _ hdr (P4A.VBits size w) st2)
                                           q)
                        =
        interp_bit_expr (WP.be_subst phi exp (BEHdr c Right (P4A.HRVar (existT _ _ hdr))))
                        valu
                        c1
                        q.
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); simpl; congruence.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        simpl.
        rewrite P4A.eq_dec_refl.
        simpl.
        rewrite P4A.eq_dec_refl.
        congruence.
      + simpl.
        destruct h.
        dependent destruction var.
        simpl in *.
        unfold P4A.find, P4A.assign.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
               | |- _ => progress unfold "===" in *
               | |- _ => progress simpl in *
               | |- _ => progress subst
               end;
          congruence.
    - reflexivity.
    - simpl.
      subst.
      erewrite IHphi; eauto.
      rewrite beslice_interp.
      reflexivity.
    - simpl.
      rewrite beconcat_interp.
      erewrite IHphi1, IHphi2; eauto.
  Qed.
  Lemma brand_interp:
    forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
      interp_store_rel (a:=a) (brand r1 r2) valu q1 q2 <->
      interp_store_rel (a:=a) (BRAnd r1 r2) valu q1 q2.
  Proof.
    intros.
    destruct r1, r2; simpl; tauto.
  Qed.
  Lemma bror_interp:
    forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
      interp_store_rel (a:=a) (bror r1 r2) valu q1 q2 <->
      interp_store_rel (a:=a) (BROr r1 r2) valu q1 q2.
  Proof.
    intros.
    destruct r1, r2; simpl; tauto.
  Qed.
  Lemma brimpl_interp:
    forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
      interp_store_rel (a:=a) (brimpl r1 r2) valu q1 q2 <->
      interp_store_rel (a:=a) (BRImpl r1 r2) valu q1 q2.
  Proof.
    intros.
    destruct r1, r2; simpl; tauto.
  Qed.
  Lemma sr_subst_hdr_left:
    forall c (valu: bval c) size (hdr: H size) exp phi c1 s1 st1 buf1 c2 (w: Ntuple.n_tuple bool size),
      conf_state c1 = s1 ->
      conf_store c1 = st1 ->
      conf_buf c1 = buf1 ->
      Ntuple.t2l w = interp_bit_expr exp valu c1 c2 ->
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEHdr c Left (P4A.HRVar (existT _ _ hdr))))
        valu
        c1
        c2 <->
      interp_store_rel
        (a:=a)
        phi
        valu
        (update_conf_store (a:=P4A.interp a)
                           (P4A.assign _ hdr (P4A.VBits size w) st1)
                           c1)
        c2.
  Proof.
    induction phi;
      simpl in *;
      erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      repeat match goal with
             | |- forall _, _ => intro
             | |- _ /\ _ => split
             | |- _ <-> _ => split
             | H: _ /\ _ |- _ => destruct H
             | H: _ <-> _ |- _ => destruct H
             | |- _ => progress subst
             end;
      try erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      simpl in *;
      try solve [erewrite !be_subst_hdr_left in *; eauto|intuition].
  Qed.
  Lemma sr_subst_hdr_right:
    forall c (valu: bval c) size (hdr: H size) exp phi c1 c2 s2 st2 buf2 (w: Ntuple.n_tuple bool size),
      conf_state c2 = s2 ->
      conf_store c2 = st2 ->
      conf_buf c2 = buf2 ->
      Ntuple.t2l w = interp_bit_expr exp valu c1 c2 ->
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEHdr c Right (P4A.HRVar (existT _ _ hdr))))
        valu
        c1
        c2 <->
      interp_store_rel
        (a:=a)
        phi
        valu
        c1
        (update_conf_store (a:=P4A.interp a)
                           (P4A.assign _ hdr (P4A.VBits size w) st2)
                           c2).
  Proof.
    induction phi;
      simpl in *;
      erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      repeat match goal with
             | |- forall _, _ => intro
             | |- _ /\ _ => split
             | |- _ <-> _ => split
             | H: _ /\ _ |- _ => destruct H
             | H: _ <-> _ |- _ => destruct H
             | |- _ => progress subst
             end;
      try erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      simpl in *;
      try solve [erewrite !be_subst_hdr_right in *; eauto|intuition].
  Qed.
  Lemma wp_op'_size:
    forall (c: bctx) si size (o: P4A.op H size) n phi m phi',
      WP.wp_op' (c:=c) si o (size + n, phi) = (m, phi') ->
      m = n.
  Proof.
    induction o; cbn; intros.
    - congruence.
    - destruct (WP.wp_op' si o2 (n1 + n2 + n, phi)) eqn:?.
      replace (n1 + n2 + n)
        with (n2 + (n1 + n))
        in *
        by Lia.lia.
      apply IHo2 in Heqp.
      subst n0.
      apply IHo1 in H0.
      eauto.
    - replace (projT1 hdr + n - projT1 hdr) with n in * by Lia.lia.
      congruence.
    - congruence.
  Qed.
  Lemma wp_op'_seq:
    forall (c: bctx) n1 n2 (o1: P4A.op H n1) (o2: P4A.op H n2) si phi,
      WP.wp_op' (c:=c) si (P4A.OpSeq o1 o2) phi = WP.wp_op' si o1 (WP.wp_op' si o2 phi).
  Proof.
    induction o1; intros; simpl;
      repeat match goal with
             | H:context [match ?x with _ => _ end] |- _ => destruct x eqn:?; simpl
             | |- context [match ?x with _ => _ end] => destruct x eqn:?; simpl
             | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
             end;
      reflexivity.
  Qed.
  Ltac break_match :=
    match goal with
    | |- context [match ?x with _ => _ end] =>
      destruct x eqn:?
    | H: context [match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
    end.
  Lemma wp_op'_mono {k}:
    forall (c: bctx) si (o: P4A.op H k) n phi,
      fst (WP.wp_op' (c:=c) si o (n, phi)) <= n.
  Proof.
    induction o; simpl.
    - Lia.lia.
    - intros.
      destruct (WP.wp_op' si o2 _) as [m psi] eqn:?.
      specialize (IHo2 n phi).
      specialize (IHo1 m psi).
      rewrite Heqp in *.
      simpl in *.
      Lia.lia.
    - Lia.lia.
    - Lia.lia.
  Qed.
  Definition projbits {n} (v: P4A.v n) :=
    match v with
    | P4A.VBits _ vec => vec
    end.
  Lemma expr_to_bit_expr_sound:
    forall (c: bctx) si (valu: bval c) n (expr: P4A.expr H n) (c1 c2: conf),
      P4A.eval_expr (S1 + S2) H a n (conf_store (match si with Left => c1 | Right => c2 end)) expr =
      P4A.VBits n (interp_bit_expr (a:=a) (WP.expr_to_bit_expr si _) valu c1 c2).
  Proof.
    assert (Hv: forall v, P4A.VBits match v with P4A.VBits v' => v' end = v).
    {
      intros.
      destruct v; reflexivity.
    }
    induction expr; intros; cbn; auto.
    - destruct (P4A.eval_expr (snd (fst _))) eqn:?.
      unfold P4A.slice.
      specialize (IHexpr c1 c2).
      simpl in IHexpr.
      rewrite -> IHexpr in Heqv.
      congruence.
  Qed.
  Lemma n_slice_slice_eq:
    forall hi lo n (x: Ntuple.n_tuple bool n),
      Ntuple.t2l (WP.P4A.n_slice _ _ a x hi lo) = P4A.slice (Ntuple.t2l x) hi lo.
  Proof.
  Admitted.
  Lemma wp_op'_spec_l:
    forall c (valu: bval c) o n phi c1 s1 st1 buf1 c2,
      P4A.nonempty o ->
      conf_state c1 = s1 ->
      conf_store c1 = st1 ->
      conf_buf c1 = buf1 ->
      interp_store_rel (a:=a)
                       (snd (WP.wp_op' Left o (n + P4A.op_size o, phi)))
                       valu
                       c1
                       c2 <->
      interp_store_rel (a:=a)
                       phi
                       valu
                       (update_conf_store (fst (P4A.eval_op _ _ a _ _ st1 buf1 o)) c1)
                       c2.
  Proof.
    induction o.
    - intros.
      simpl.
      reflexivity.
    - intros.
      destruct H0.
      simpl (P4A.eval_op _ _ _ _).
      destruct (P4A.eval_op st1 n buf1 o1) as [st1' n'] eqn:?.
      destruct (P4A.eval_op st1' n' buf1 o2) as [st2' n''] eqn:?.
      pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
      pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
      simpl (WP.wp_op' _ _ _).
      destruct (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
      assert (wn' = P4A.op_size o1 + n).
      {
        replace (n + (P4A.op_size o1 + P4A.op_size o2))
          with (P4A.op_size o2 + (P4A.op_size o1 + n))
          in Heqp1
          by Lia.lia.
        eapply wp_op'_size.
        eauto.
      }
      subst wn'.
      replace (P4A.op_size o1 + n)
        with (n + P4A.op_size o1)
        by Lia.lia.
      erewrite IHo1 by eauto.
      rewrite Heqp; simpl.
      replace st2' with (fst (P4A.eval_op st1' n' buf1 o2))
        by (rewrite Heqp0; reflexivity).
      replace phi' with (snd (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
        by (rewrite Heqp1; reflexivity).
      rewrite Plus.plus_assoc.
      erewrite IHo2 by eauto.
      subst n'.
      rewrite Heqp0.
      reflexivity.
    - simpl.
      intros.
      rewrite sr_subst_hdr_left.
      simpl.
      replace (n + width - width) with n by Lia.lia.
      simpl.
      unfold P4A.slice.
      replace (1 + (n + width - 1)) with (n + width)
        by Lia.lia.
      erewrite <- firstn_skipn_comm.
      reflexivity.
    - simpl.
      unfold WP.wp_op, WP.wp_op'.
      simpl.
      intros.
      destruct lhs.
      rewrite sr_subst_hdr_left.
      simpl.
      rewrite <- expr_to_bit_expr_sound.
      reflexivity.
  Qed.
  (* This is basically a copy-pasted version of wp_op'_spec_l with
      some things flipped around. *)
  Lemma wp_op'_spec_r:
    forall c (valu: bval c) o n phi s2 st2 buf2 c1,
      P4A.nonempty o ->
      interp_store_rel (a:=a)
                       (snd (WP.wp_op' Right o (n + P4A.op_size o, phi)))
                       valu
                       c1
                       (s2, st2, buf2)
      <->
      interp_store_rel (a:=a)
                       phi
                       valu
                       c1
                       (s2,
                        fst (P4A.eval_op st2 n buf2 o),
                        buf2).
  Proof.
    induction o.
    - intros.
      simpl.
      reflexivity.
    - intros.
      destruct H0.
      simpl (P4A.eval_op _ _ _ _).
      destruct (P4A.eval_op st2 n buf2 o1) as [st2' n'] eqn:?.
      destruct (P4A.eval_op st2' n' buf2 o2) as [st2'' n''] eqn:?.
      pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
      pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
      simpl (WP.wp_op' _ _ _).
      destruct (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
      assert (wn' = P4A.op_size o1 + n).
      {
        replace (n + (P4A.op_size o1 + P4A.op_size o2))
          with (P4A.op_size o2 + (P4A.op_size o1 + n))
          in Heqp1
          by Lia.lia.
        eapply wp_op'_size.
        eauto.
      }
      subst wn'.
      replace (P4A.op_size o1 + n)
        with (n + P4A.op_size o1)
        by Lia.lia.
      erewrite IHo1 by eauto.
      rewrite Heqp; simpl.
      replace st2'' with (fst (P4A.eval_op st2' n' buf2 o2))
        by (rewrite Heqp0; reflexivity).
      replace phi' with (snd (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
        by (rewrite Heqp1; reflexivity).
      rewrite Plus.plus_assoc.
      erewrite IHo2 by eauto.
      subst n'.
      rewrite Heqp0.
      reflexivity.
    - simpl.
      intros.
      rewrite sr_subst_hdr_right.
      simpl.
      replace (n + width - width) with n by Lia.lia.
      simpl.
      unfold P4A.slice.
      replace (1 + (n + width - 1)) with (n + width)
        by Lia.lia.
      erewrite <- firstn_skipn_comm.
      reflexivity.
    - simpl.
      unfold WP.wp_op, WP.wp_op'.
      simpl.
      intros.
      destruct lhs.
      rewrite sr_subst_hdr_right.
      simpl.
      rewrite <- expr_to_bit_expr_sound.
      reflexivity.
  Qed.
  Definition pred_top {c} (p1 p2: WP.pred S1 S2 H c) : Prop :=
    forall q1 q2,
      match p1 with
      | WP.PredRead _ _ st =>
        interp_state_template st q1
      | WP.PredJump phi s =>
        fst (fst q1) = s
      end ->
      match p2 with
      | WP.PredRead _ _ st =>
        interp_state_template st q2
      | WP.PredJump phi s =>
        fst (fst q2) = s
      end ->
      top q1 q2.
  Lemma wp_pred_pair_step :
    forall C u v,
      SynPreSynWP.topbdd _ _ _ a top (interp_conf_rel C) ->
      (forall sl sr,
          pred_top sl sr ->
          interp_crel (a:=a) top (WP.wp_pred_pair a C (sl, sr)) u v) ->
      (forall b, interp_conf_rel C (step u b) (step v b)).
  Proof.
    intros.
    unfold WP.wp_pred_pair in *.
    destruct u as [[us ust] ubuf].
    destruct v as [[vs vst] vbuf].
    unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template in * |-.
    destruct C as [[[Cst1 Clen1] [Cst2 Cbuf2]] Cctx Crel].
    unfold interp_conf_rel, interp_conf_state, interp_state_template.
    intros.
    simpl (st_state _) in *.
    simpl (st_buf_len _) in *.
    simpl (PreBisimulationSyntax.cr_st _) in *.
    simpl (PreBisimulationSyntax.cr_ctx _) in *.
    simpl (PreBisimulationSyntax.cr_rel _) in *.
    destruct H2 as [? [? [? [? [? ?]]]]].
    subst.
    unfold step; cbn.
    simpl in *.
    repeat match goal with
    | |- context [length (?x ++ [_])] =>
      replace (length (x ++ [_])) with (S (length x)) in *
        by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
    end.
    destruct vs as [vs | vs], us as [us | us]; simpl.
    simpl in * |-.
    destruct (equiv_dec (S (length ubuf)) (P4A.size a us)),
             (equiv_dec (S (length vbuf)) (P4A.size a vs)).
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  Lemma be_subst_buf_left:
    forall c (valu: bval c) exp phi c2 s1 st1 buf1 v,
      interp_bit_expr exp valu (s1, st1, buf1) c2 = v ->
      interp_bit_expr (a:=a) phi valu
                      (s1, st1, v)
                      c2
      =
      interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Left))
                      valu
                      (s1, st1, buf1)
                      c2.
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        reflexivity.
      + simpl.
        unfold P4A.find, P4A.Env.find, P4A.assign.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
               | |- _ => progress simpl in *
               end;
          congruence.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); try congruence.
      simpl.
      destruct a0; simpl;
        destruct (P4A.find _ _);
        reflexivity.
    - simpl.
      eauto.
    - simpl.
      rewrite beslice_interp.
      simpl.
      admit.
    - simpl.
      erewrite IHphi1, IHphi2; auto.
  Admitted.
  Lemma be_subst_buf_right:
    forall c (valu: bval c) exp phi c1 s2 st2 buf2 v,
      interp_bit_expr exp valu c1 (s2, st2, buf2) = v ->
      interp_bit_expr (a:=a) phi valu
                      c1
                      (s2, st2, v)
      =
      interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Right))
                      valu
                      c1
                      (s2, st2, buf2).
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        reflexivity.
      + simpl.
        unfold P4A.find, P4A.Env.find, P4A.assign.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
               | |- _ => progress simpl in *
               end;
          congruence.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); try congruence.
      simpl.
      destruct a0; simpl;
        destruct (P4A.find _ _);
        reflexivity.
    - simpl.
      eauto.
    - simpl.
      erewrite IHphi; eauto.
      admit.
    - simpl.
      erewrite IHphi1, IHphi2; auto.
      admit.
  Admitted.
  Lemma sr_subst_buf_left:
    forall c (valu: bval c) exp phi s1 st1 buf1 c2,
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEBuf _ c Left))
        valu
        (s1, st1, buf1)
        c2 <->
      interp_store_rel
        (a:=a)
        phi
        valu
        (s1,
         st1,
         interp_bit_expr exp valu (s1, st1, buf1) c2)
        c2.
  Proof.
    induction phi; simpl in *; try tauto; split; intros;
      rewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      try solve [erewrite <- ?be_subst_buf_left in *;
                 eauto
                |simpl in *; intuition].
  Qed.
  Lemma sr_subst_buf_right:
    forall c (valu: bval c) exp phi c1 s2 st2 buf2,
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEBuf _ c Right))
        valu
        c1
        (s2, st2, buf2) <->
      interp_store_rel
        (a:=a)
        phi
        valu
        c1
        (s2,
         st2,
         interp_bit_expr exp valu c1 (s2, st2, buf2)).
  Proof.
    induction phi; simpl in *; try tauto; split; intros;
      rewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *;
      try solve [erewrite <- ?be_subst_buf_right in *;
                 eauto
                |simpl in *; intuition].
  Qed.
  Lemma interp_bit_expr_ignores_state:
    forall {c} (e: bit_expr H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
      interp_bit_expr (a:=a) e valu (s1, st1, buf1) (s2, st2, buf2) =
      interp_bit_expr (a:=a) e valu (s1', st1, buf1) (s2', st2, buf2).
  Proof.
    induction e; intros.
    - reflexivity.
    - reflexivity.
    - simpl.
      destruct a0; simpl; reflexivity.
    - reflexivity.
    - simpl.
      erewrite IHe; eauto.
    - simpl.
      erewrite IHe1, IHe2; eauto.
  Qed.
  Lemma interp_store_rel_ignores_state:
    forall {c} (r: store_rel H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
      interp_store_rel (a:=a) r valu (s1, st1, buf1) (s2, st2, buf2) ->
      interp_store_rel (a:=a) r valu (s1', st1, buf1) (s2', st2, buf2).
  Proof.
    induction r; intros; simpl in *; try solve [intuition eauto].
    erewrite (interp_bit_expr_ignores_state e1).
    erewrite (interp_bit_expr_ignores_state e2).
    eauto.
  Qed.
  Lemma wp_concrete_safe :
    SynPreSynWP.safe_wp_1bit _ _ _ a (WP.wp (H:=H)) top.
  Proof.
    unfold SynPreSynWP.safe_wp_1bit.
    intros.
    destruct q1 as [[st1 s1] buf1].
    destruct q2 as [[st2 s2] buf2].
    unfold WP.wp in * |-.
    destruct C.
    destruct a; simpl in * |-.
    destruct cr_st.
    unfold WP.wp in * |-.
    (*
eier the step is a jump or a read on the left and on the right
sohat's a total of 4 cases.
Buin each case you need to massage the WP to line up with it,
beuse you're not branching on the same thing.
*)
    unfold step.
    unfold interp_conf_rel, interp_conf_state, interp_state_template; intros.
    simpl in *.
    intuition.
    simpl in *.
    repeat match goal with
    | |- context [length (?x ++ [_])] =>
      replace (length (x ++ [_])) with (S (length x)) in *
        by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
    end.
    destruct (equiv_dec (S (length buf1)) _), (equiv_dec (S (length buf2)) _);
      unfold "===" in *;
      simpl in *.
    - cbv in H0.
      destruct cs_st1 as [cst1 bl1] eqn:?, cs_st2 as [cst2 bl2] eqn:?.
      simpl in *.
      (* this is a real transition*)
      destruct st1 as [[st1 | ?] | st1], st2 as [[st2 | ?] | st2];
        try solve [cbv in H0; tauto].
      + simpl in *.
        admit.
        (* subst bl2.
        subst bl1.
        simpl in *. *)
        (* admit. *)
      + admit.
      + admit.
      + simpl in *.
        admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - admit.
    - admit.
    - (* easiest case probably *)
      admit.
  Admitted.
  Lemma syn_pre_1bit_concrete_implies_sem_pre:
  forall R S q1 q2,
    SynPreSynWP.ctopbdd _ _ _ a top R ->
    SynPreSynWP.ctopbdd _ _ _ a top S ->
    SynPreSynWP.pre_bisimulation a (WP.wp (H:=H)) top R S q1 q2 ->
    SemPre.pre_bisimulation (P4A.interp a)
                            top
                            (map interp_conf_rel R)
                            (map interp_conf_rel S)
                            q1 q2.
  Proof.
    eauto using wp_concrete_safe, wp_concrete_bdd, SynPreSynWP.syn_pre_implies_sem_pre.
  Qed.

*)
End WPProofs.

