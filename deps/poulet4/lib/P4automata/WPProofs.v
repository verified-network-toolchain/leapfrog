Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Ntuple.
Require Import Poulet4.P4automata.NtupleProofs.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.WP.
Require Import Poulet4.P4automata.Bisimulations.Leaps.

Section WPProofs.
  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := (S1 + S2)%type.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
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
      @be_size H ctx b1 b2 (beslice e hi lo) =
      @be_size H ctx b1 b2 (BESlice e hi lo).
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
    forall ctx (e: bit_expr H ctx) hi lo valu
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           (store1 store2: store (P4A.interp a)),
      JMeq
        (interp_bit_expr (beslice e hi lo) valu buf1 buf2 store1 store2)
        (interp_bit_expr (BESlice e hi lo) valu buf1 buf2 store1 store2).
  Proof.
    induction e; intros;
      repeat (progress cbn
              || autorewrite with interp_bit_expr
              || rewrite rewrite_size_eq);
      eauto.
    - apply slice_n_tuple_slice_eq.
    - admit.
  Admitted.

  Lemma beconcat_interp_length:
    forall ctx (e1 e2: bit_expr H ctx) l1 l2,
      be_size l1 l2 (beconcat e1 e2) = be_size l1 l2 (BEConcat e1 e2).
  Proof.
    induction e1; destruct e2; intros; simpl; auto.
    apply app_length.
  Qed.

  Lemma beconcat_interp:
    forall ctx (e1 e2: bit_expr H ctx) valu
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           (store1 store2: store (P4A.interp a)),
      JMeq (interp_bit_expr (beconcat e1 e2) valu buf1 buf2 store1 store2)
           (interp_bit_expr (BEConcat e1 e2) valu buf1 buf2 store1 store2).
  Proof.
    induction e1; destruct e2; intros; simpl; auto.
    autorewrite with interp_bit_expr.
    eauto using l2t_app.
  Qed.

  Lemma be_subst_be_size:
    forall c l1 l2 h phi (exp: bit_expr H c),
      be_size l1 l2 h = be_size l1 l2 exp ->
      be_size l1 l2 phi = be_size l1 l2 (be_subst phi exp h).
  Proof.
    induction phi; intros; simpl;
      repeat match goal with
             | H: context[ match ?e with _ => _ end ] |- _ =>
               destruct e eqn:?
             | |- context[ match ?e with _ => _ end ] =>
               destruct e eqn:?
             | |- context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] =>
               progress (destruct (@EquivDec.equiv_dec A R e E x y))
             | H: context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] |- _ =>
               progress (destruct (@EquivDec.equiv_dec A R e E x y))
             | H: left _ = left _ |- _ => injection H; clear H
             | |- _ => progress subst
             | |- _ => progress unfold eq_rect in *
             | |- _ => progress rewrite !P4A.eq_dec_refl in *
             | |- _ => progress cbn in *
             | |- _ => rewrite !beslice_interp_length in *
             | |- _ => rewrite !beconcat_interp_length in *
             end;
      solve [congruence
            |erewrite <- IHphi in *; auto; congruence
            |erewrite <- IHphi1, IHphi2 in *; auto; congruence].
  Qed.

  Lemma inv_jmeq_size:
    forall n (xs: n_tuple bool n) m (ys: n_tuple bool m),
      xs ~= ys ->
      n = m.
  Proof.
    intros.
    eapply n_tuple_inj.
    now inversion H0.
  Qed.

  Lemma t2l_n_eq:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    t2l xs = t2l ys ->
    n = m.
  Proof.
    intros.
    pose proof (t2l_len n xs).
    pose proof (t2l_len m ys).
    congruence.
  Qed.

  Lemma t2l_eq:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    t2l xs = t2l ys ->
    xs ~= ys.
  Proof.
    intros.
    pose proof (t2l_n_eq _ _ _ _ H0).
    subst m.
    cut (xs = ys).
    {
      intros.
      subst.
      reflexivity.
    }
    induction n; cbn in *; destruct xs, ys; cbn in *.
    - reflexivity.
    - assert (b = b0).
      {
        apply f_equal with (f := (fun l => (@last bool) l false)) in H0.
        erewrite !last_last in H0.
        congruence.
      }
      subst b0.
      apply app_inv_tail in H0.
      apply IHn in H0.
      congruence.
  Qed.

  Lemma eq_t2l:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    xs ~= ys ->
    t2l xs = t2l ys.
  Proof.
    intros.
    inversion H0.
    assert (n = m) by auto using n_tuple_inj.
    subst m.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma n_tuple_cons_inj_r:
    forall n m (xs: n_tuple bool n) x (ys: n_tuple bool m) y,
      n_tuple_cons xs x ~= n_tuple_cons ys y ->
      xs ~= ys /\ x = y.
  Proof.
    induction n; intros.
    - destruct m.
      + simpl_JMeq.
        destruct xs, ys.
        cbn in *.
        intuition congruence.
      + exfalso.
        apply inv_jmeq_size in H0.
        Lia.lia.
    - destruct m, xs; destruct ys.
      + exfalso.
        apply inv_jmeq_size in H0.
        Lia.lia.
      + pose proof (inv_jmeq_size _ _ _ _ H0).
        assert (n = m) by Lia.lia.
        subst m.
        simpl_JMeq.
        simpl in *.
        inversion H0.
        subst b0.
        pose proof (IHn _ n0 x n1 y ltac:(rewrite H3; reflexivity)).
        destruct H2.
        split; [|auto].
        rewrite H2.
        reflexivity.
  Qed.

  Lemma slice_proper:
    forall hi lo n m (xs: n_tuple bool n) (ys: n_tuple bool m),
      xs ~= ys ->
      n_tuple_slice hi lo xs ~= n_tuple_slice hi lo ys.
  Proof.
    intros hi lo n m xs ys Heq.
    assert (n = m)
      by (eapply inv_jmeq_size; eauto).
    revert Heq.
    revert xs ys.
    subst m.
    intros.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma concat_proper:
    forall n1 m1 (xs1: n_tuple bool n1) (ys1: n_tuple bool m1)
      n2 m2 (xs2: n_tuple bool n2) (ys2: n_tuple bool m2),
      xs1 ~= xs2 ->
      ys1 ~= ys2 ->
      n_tuple_concat xs1 ys1 ~= n_tuple_concat xs2 ys2.
  Proof.
    intros.
    assert (n1 = n2) by (eapply inv_jmeq_size; eauto).
    assert (m1 = m2) by (eapply inv_jmeq_size; eauto).
    revert H0 H1.
    revert xs2 ys2.
    revert xs1 ys1.
    subst n2.
    subst m2.
    intros.
    rewrite H0.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma be_subst_hdr_left:
    forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) c2 (w: Ntuple.n_tuple bool size),
        interp_bit_expr exp valu q.(conf_buf) c2.(conf_buf) q.(conf_store) c2.(conf_store) ~= w ->
        interp_bit_expr (a:=a) phi valu
                        q.(conf_buf)
                        c2.(conf_buf)
                        (update_conf_store (a:=P4A.interp a)
                                           (P4A.assign _ hdr (P4A.VBits size w) q.(conf_store))
                                           q).(conf_store)
                        c2.(conf_store)
        ~=
        interp_bit_expr (WP.be_subst phi exp (BEHdr c Left (P4A.HRVar (existT _ _ hdr))))
                        valu
                        q.(conf_buf)
                        c2.(conf_buf)
                        q.(conf_store)
                        c2.(conf_store).
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); simpl.
      + inversion e.
      + destruct a0; autorewrite with interp_bit_expr; eauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        autorewrite with interp_bit_expr.
        simpl.
        unfold P4A.find.
        cbn.
        rewrite P4A.eq_dec_refl.
        simpl.
        rewrite P4A.eq_dec_refl.
        apply JMeq_sym.
        auto.
      + destruct h as [[hsize h]].
        autorewrite with interp_bit_expr in *.
        unfold P4A.find, P4A.assign.
        cbn in *.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ =>
                 destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] =>
                 destruct e eqn:?
               | |- context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] =>
                 progress (destruct (@EquivDec.equiv_dec A R e E x y))
               | H: context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] |- _ =>
                 progress (destruct (@EquivDec.equiv_dec A R e E x y))
               | |- _ => progress unfold eq_rect in *
               | |- _ => progress rewrite !P4A.eq_dec_refl in *
               | |- _ => progress cbn in *
               | |- _ => progress subst
               | |- ?x ~= ?y =>
                 try (cut (x = y); [intros; subst; now constructor|]; congruence)
               | |- _ => try congruence
               end.
    - reflexivity.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      rewrite beslice_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H0).
      match goal with
      | |- n_tuple_slice hi lo ?x ~= n_tuple_slice hi lo ?y =>
        set (iu := x);
          set (ss := y);
          cut (iu ~= ss);
          solve [apply slice_proper|now apply IHphi]
      end.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      rewrite beconcat_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H0).
      match goal with
      | |- n_tuple_concat ?xs1 ?ys1 ~= n_tuple_concat ?xs2 ?ys2 =>
          cut (xs1 ~= xs2 /\ ys1 ~= ys2);
          [|split]
      end.
      + intros [? ?].
        eapply concat_proper; eauto.
      + now apply IHphi1.
      + now apply IHphi2.
  Qed.

  Lemma be_subst_hdr_right:
    forall c (valu: bval c) size (hdr: H size) exp phi (q: conf) c1 (w: Ntuple.n_tuple bool size),
        interp_bit_expr exp valu c1.(conf_buf) q.(conf_buf) c1.(conf_store) q.(conf_store) ~= w ->
        interp_bit_expr (a:=a) phi valu
                        c1.(conf_buf)
                        q.(conf_buf)
                        c1.(conf_store)
                        (update_conf_store (a:=P4A.interp a)
                                           (P4A.assign _ hdr (P4A.VBits size w) q.(conf_store))
                                           q).(conf_store)

        ~=
        interp_bit_expr (WP.be_subst phi exp (BEHdr c Right (P4A.HRVar (existT _ _ hdr))))
                        valu
                        c1.(conf_buf)
                        q.(conf_buf)
                        c1.(conf_store)
                        q.(conf_store).
  Proof.
    induction phi; intros.
    - tauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _); simpl.
      + inversion e.
      + destruct a0; autorewrite with interp_bit_expr; eauto.
    - unfold WP.be_subst.
      destruct (bit_expr_eq_dec _ _).
      + inversion e; clear e; subst.
        autorewrite with interp_bit_expr.
        simpl.
        unfold P4A.find.
        cbn.
        rewrite P4A.eq_dec_refl.
        simpl.
        rewrite P4A.eq_dec_refl.
        apply JMeq_sym.
        auto.
      + destruct h as [[hsize h]].
        autorewrite with interp_bit_expr in *.
        unfold P4A.find, P4A.assign.
        cbn in *.
        repeat match goal with
               | H: context[ match ?e with _ => _ end ] |- _ =>
                 destruct e eqn:?
               | |- context[ match ?e with _ => _ end ] =>
                 destruct e eqn:?
               | |- context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] =>
                 progress (destruct (@EquivDec.equiv_dec A R e E x y))
               | H: context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] |- _ =>
                 progress (destruct (@EquivDec.equiv_dec A R e E x y))
               | |- _ => progress unfold eq_rect in *
               | |- _ => progress rewrite !P4A.eq_dec_refl in *
               | |- _ => progress cbn in *
               | |- _ => progress subst
               | |- ?x ~= ?y =>
                 try (cut (x = y); [intros; subst; now constructor|]; congruence)
               | |- _ => try congruence
               end.
    - reflexivity.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      rewrite beslice_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H0).
      match goal with
      | |- n_tuple_slice hi lo ?x ~= n_tuple_slice hi lo ?y =>
        set (iu := x);
          set (ss := y);
          cut (iu ~= ss);
          [apply slice_proper|now apply IHphi]
      end.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      rewrite beconcat_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H0).
      match goal with
      | |- n_tuple_concat ?xs1 ?ys1 ~= n_tuple_concat ?xs2 ?ys2 =>
          cut (xs1 ~= xs2 /\ ys1 ~= ys2);
          [|split]
      end.
      + intros [? ?].
        eapply concat_proper; eauto.
      + now apply IHphi1.
      + now apply IHphi2.
  Qed.

  (*
  Lemma brand_interp:
    forall ctx (r1 r2: store_rel _ ctx) valu q1 q2,
      interp_store_rel (a:=a) (brand r1 r2) valu q1 q2 <->
      interp_store_rel (a:=a) (BRAnd r1 r2) valu q1 q2.
  Proof.
    intros.
    destruct r1, r2; simpl; auto.
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
*)

  Lemma wp_bounded:
    forall top phi phi' q1 q2,
      In phi' (wp (a:=a) top phi) ->
      interp_conf_rel a phi' q1 q2 ->
      interp_tpairs top q1 q2.
  Proof.
  Admitted.

  Lemma reachable_step_size:
    forall prev size s,
      Reachability.reachable_pair_step' prev = (size, s) ->
      size = Reachability.reads_left (a:=a) prev.
  Proof.
    unfold Reachability.reachable_pair_step'.
    intros.
    destruct prev.
    congruence.
  Qed.

  Lemma reaches_length:
    forall size cur prev,
      In (size, prev) (reaches (a:=a) cur prev) ->
      size = Reachability.reads_left prev.
  Proof.
    unfold reaches.
    intros.
    destruct (Reachability.reachable_pair_step' _) eqn:?.
    destruct (in_dec _ _); simpl in *; [eauto with datatypes | tauto].
    destruct H0; [|tauto].
    inversion H0; subst.
    eapply reachable_step_size; eauto.
  Qed.

  Lemma reaches_exists:
    forall cur prev size l,
      Reachability.reachable_pair_step' prev = (size, l) ->
      In cur l ->
      In (size, prev) (reaches (a:=a) cur prev).
  Proof.
    unfold reaches.
    intros.
    destruct (Reachability.reachable_pair_step' _).
    inversion H0; subst.
    destruct (in_dec _ _); [eauto with datatypes | tauto].
  Qed.

  Lemma reaches_prev:
    forall cur prev prev' size,
      In (size, prev') (reaches (a:=a) cur prev) ->
      prev' = prev.
  Proof.
    unfold reaches.
    intros.
    destruct (Reachability.reachable_pair_step' _) in H0.
    destruct (in_dec _ _) in H0.
    - simpl in *; destruct H0.
      + congruence.
      + tauto.
    - simpl in H0; tauto.
  Qed.

  Lemma reads_left_config_left:
    forall st1 st2 (q1 q2: conf),
      interp_state_template st1 q1 ->
      interp_state_template st2 q2 ->
      Reachability.reads_left (a:=a) (st1, st2) =
      leap_size (P4A.interp a) q1 q2.
  Proof.
    unfold interp_state_template.
    unfold Reachability.reads_left.
    unfold leap_size.
    unfold configuration_room_left.
    intuition.
    rewrite !H2, !H3, !H0, !H4.
    destruct (conf_state q1), (conf_state q2); auto.
  Qed.

  Lemma wp_pred_pair_safe:
    forall size top phi t1 t2 q1 q2,
      interp_crel a top (wp_pred_pair (a:=a) phi (size, (t1, t2))) q1 q2 ->
      forall bs,
        length bs = size ->
        interp_conf_rel a phi (follow q1 bs) (follow q2 bs).
  Proof.
    unfold wp_pred_pair.
    intros.
    simpl in *; destruct H0; try tauto.
    unfold interp_conf_rel, interp_conf_state, interp_state_template in H1.
    simpl in *.
  Admitted.

  Lemma reachable_step_backwards:
    forall st st' bs sts q1 q2,
      Reachability.reachable_pair_step' st' = (length bs, sts) ->
      In st sts ->
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st; cs_st2 := snd st|}
                        (follow q1 bs)
                        (follow q2 bs) ->
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st'; cs_st2 := snd st'|}
                        q1
                        q2.
  Proof.
    intros [st1 st2] [st1' st2'].
    unfold Reachability.reachable_pair_step'.
    intros.
    set (k := Reachability.reads_left (st1', st2')) in *.
    inversion H0.
    subst sts.
    clear H0.
    apply in_prod_iff in H1.
    unfold interp_conf_state; cbn; intuition.
    - admit.
    - admit.
  Admitted.

  Lemma wp_template_complete:
    forall st st' q1 q2 bs,
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st; cs_st2 := snd st|}
                        (follow q1 bs) (follow q2 bs) ->
      In (length bs, st') (reaches st st') ->
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st'; cs_st2 := snd st'|}
                        q1 q2.
  Proof.
    intros [st1 st2] [st1' st2'] q1 q2 bs.
    unfold reaches.
    intros.
    destruct (Reachability.reachable_pair_step' _) eqn:?.
    destruct (in_dec _ _); simpl in H1; intuition.
    inversion H2; subst n.
    eapply reachable_step_backwards; eauto.
  Qed.

  Lemma follow_in_reaches:
    forall bs prev s1 s2 p1 p2 prev1 prev2,
      length bs = leap_size (P4A.interp a) p1 p2 ->
      interp_state_template prev1 p1 ->
      interp_state_template prev2 p2 ->
      interp_state_template s1 (follow p1 bs) ->
      interp_state_template s2 (follow p2 bs) ->
      In (length bs, prev) (reaches (a:=a) (s1, s2) (prev1, prev2)).
  Proof.
  Admitted.

  Definition conf2st (q: conf) : state_template a :=
    {| st_state := conf_state q;
       st_buf_len := conf_buf_len q |}.

  (* prove this first *)
  Theorem wp_safe:
    forall top r phi q1 q2,
      In (conf2st q1, conf2st q2) r ->
      interp_crel a top (wp (a := a) r phi) q1 q2 ->
      forall bs,
        List.length bs = leap_size (P4A.interp a) q1 q2 ->
        interp_conf_rel a phi (follow q1 bs) (follow q2 bs).
  Proof.
    intros.
    set (q1' := follow q1 bs) in *.
    set (q2' := follow q2 bs) in *.
    unfold interp_conf_rel.
    intros.
    destruct phi as [[phi_st1 phi_st2] phi_ctx phi_rel] eqn:?; cbn in *.
    simpl.
    intros.
    intuition.
    unfold wp in H0.
    simpl in *.
    set (r' := flat_map (wp_pred_pair phi)
                       (flat_map (reaches (phi_st1, phi_st2))
                                 r))
      in *.
    unfold interp_crel in H0.
    assert (forall size st,
               In st r ->
               In (size, st)
                  (reaches (cs_st1 (cr_st phi), cs_st2 (cr_st phi)) st) ->
               forall r',
                 In r' (wp_pred_pair phi (size, st)) ->
                 interp_conf_rel a r' q1 q2).
    {
      subst phi.
      pose proof (Relations.interp_rels_in _ _ _ _ _ H1).
      setoid_rewrite in_map_iff in H4.
      intros.
      subst r'.
      repeat setoid_rewrite in_flat_map in H4.
      simpl in *.
      eapply H4.
      destruct st in *; simpl in *.
      intuition.
      subst r'0.
      eexists; intuition eauto.
      eexists; intuition eauto.
      simpl.
      intuition.
    }
    set (st1 := {| st_state := conf_state q1;
                   st_buf_len := conf_buf_len q1|}).
    set (st2 := {| st_state := conf_state q2;
                   st_buf_len := conf_buf_len q2|}).
    set (qst := {|cs_st1 := st1; cs_st2 := st2|}).
    change phi_st1 with (fst (phi_st1, phi_st2)) in H2.
    change phi_st2 with (snd (phi_st1, phi_st2)) in H2.
    destruct (Reachability.reachable_pair_step' (st1, st2)) eqn:?.
    assert (In (length bs, (st1, st2)) (reaches (a:=a) (phi_st1, phi_st2) (st1, st2))).
    {
      eapply follow_in_reaches with (p1 := q1) (p2 := q2);
        try solve [cbv; tauto
                  |unfold interp_conf_state in H3;
                   subst q1' q2';
                   simpl in H3;
                   tauto].
    }
    assert (Hpairq: interp_crel a top (wp_pred_pair phi (length bs, (st1, st2))) q1 q2).
    {
      unfold interp_crel.
      apply Relations.in_interp_rels.
      - eapply Relations.interp_rels_bound; eauto.
      - pose proof (Relations.interp_rels_in _ _ _ _ _ H1).
        intros.
        rewrite in_map_iff in H7.
        destruct H7 as [cr [? ?]].
        eapply H6.
        subst r0.
        rewrite in_map_iff.
        eexists; intuition.
        apply in_flat_map.
        subst phi.
        eexists; intuition.
        apply in_flat_map.
        exists (st1, st2).
        intuition eauto.
    }
    eapply (wp_pred_pair_safe (length bs) top phi st1 st2 q1 q2) in Hpairq; eauto.
    unfold interp_conf_rel in Hpairq.
    subst phi q1' q2'.
    eauto.
  Qed.

  (* prove this later *)
  Theorem wp_complete:
    forall top r phi q1 q2,
      (forall bs,
        List.length bs = leap_size (P4A.interp a) q1 q2 ->
        interp_conf_rel a phi (follow q1 bs) (follow q2 bs)) ->
      interp_crel a top (wp (a := a) r phi) q1 q2.
  Proof.
  Admitted.

  (*
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
