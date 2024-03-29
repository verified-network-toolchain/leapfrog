Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Require Import Leapfrog.FinType.
Require Import Leapfrog.Ntuple.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.WP.
Require Import Leapfrog.Bisimulations.Leaps.

Set Universe Polymorphism.

Section WPProofs.
  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  Notation St := (St1 + St2)%type.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> nat).

  Variable (a: P4A.t St Hdr_sz).
  Notation conf := (configuration (P4A.interp a)).

  Definition pick {A} (s: side) (x: A * A) :=
    match s with
    | Left => fst x
    | Right => snd x
    end.

  Definition pick_dep {A B: Type} (s: side) (x: A * B) : pick s (A, B) :=
    match s as s return pick s (A, B) with
    | Left => fst x
    | Right => snd x
    end.

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
      @be_size Hdr Hdr_sz ctx b1 b2 (beslice e hi lo) =
      @be_size Hdr Hdr_sz ctx b1 b2 (BESlice e hi lo).
  Proof.
    intros.
    unfold beslice.
    destruct e; eauto.
    - unfold be_size.
      rewrite P4A.slice_len.
      Lia.lia.
    - unfold be_size.
      fold (be_size Hdr_sz b1 b2 e).
      Lia.lia.
  Qed.

  Lemma t2l_n_tuple_slice:
    forall n hi lo (t: n_tuple bool n),
      t2l (n_tuple_slice hi lo t) = P4A.slice (t2l t) hi lo.
  Proof.
    intros.
    unfold n_tuple_slice.
    unfold P4A.slice.
    now rewrite t2l_n_tuple_skip_n, t2l_n_tuple_take_n.
  Qed.

  Lemma slice_n_tuple_slice_eq:
    forall (l: list bool) hi lo,
      l2t (ConfRel.P4A.slice l hi lo) ~=
      n_tuple_slice hi lo (l2t l).
  Proof.
    intros.
    replace l with (t2l (l2t l)) by (now rewrite t2l_l2t).
    rewrite <- t2l_n_tuple_slice.
    pose proof (t2l_l2t _ l).
    rewrite !H.
    eapply JMeq_trans.
    eapply l2t_t2l.
    reflexivity.
  Qed.

  Lemma beslice_interp:
    forall ctx (e: bit_expr Hdr ctx) hi lo valu
           b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2)
           (store1 store2: store (P4A.interp a)),
      interp_bit_expr (beslice e hi lo) valu buf1 buf2 store1 store2 ~=
      interp_bit_expr (BESlice e hi lo) valu buf1 buf2 store1 store2.
  Proof.
    intros; destruct e; unfold beslice; autorewrite with interp_bit_expr; auto.
    - apply slice_n_tuple_slice_eq.
    - generalize (interp_bit_expr e valu buf1 buf2 store1 store2) as t; intros.
      apply t2l_eq.
      unfold be_size; fold (be_size Hdr_sz b1 b2 e).
      repeat rewrite t2l_n_tuple_slice.
      now rewrite slice_slice.
  Qed.

  Lemma beconcat_interp_length:
    forall ctx (e1 e2: bit_expr Hdr ctx) l1 l2,
      be_size Hdr_sz l1 l2 (beconcat e1 e2) = be_size Hdr_sz l1 l2 (BEConcat e1 e2).
  Proof.
    induction e1; destruct e2; intros; simpl; auto.
    apply app_length.
  Qed.

  Lemma beconcat_interp:
    forall ctx (e1 e2: bit_expr Hdr ctx) valu
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
    forall c l1 l2 h phi (exp: bit_expr Hdr c),
      be_size Hdr_sz l1 l2 h = be_size Hdr_sz l1 l2 exp ->
      be_size Hdr_sz l1 l2 phi = be_size Hdr_sz l1 l2 (be_subst phi exp h).
  Proof.
    induction phi; intros; simpl;
      repeat match goal with
             | Hdr: context[ match ?e with _ => _ end ] |- _ =>
               destruct e eqn:?
             | |- context[ match ?e with _ => _ end ] =>
               destruct e eqn:?
             | |- context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] =>
               progress (destruct (@EquivDec.equiv_dec A R e E x y))
             | Hdr: context[ EquivDec.equiv_dec ?A ?R ?e ?E ?x ?y ] |- _ =>
               progress (destruct (@EquivDec.equiv_dec A R e E x y))
             | Hdr: left _ = left _ |- _ => injection Hdr; clear Hdr
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

  Lemma be_subst_hdr_left:
    forall c (valu: bval c) (hdr: Hdr) exp phi
      st1
      bs1
      (buf1: Ntuple.n_tuple bool bs1)
      st2
      bs2
      (buf2: Ntuple.n_tuple bool bs2)
      (w: Ntuple.n_tuple bool (Hdr_sz hdr)),
      interp_bit_expr exp valu buf1 buf2 st1 st2 ~= w ->
      interp_bit_expr (a:=a) phi valu
                      buf1
                      buf2
                      (P4A.assign _ Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1)
                      st2
      ~=
      interp_bit_expr (WP.be_subst phi exp (BEHdr c Left (P4A.HRVar hdr)))
                      valu
                      buf1
                      buf2
                      st1
                      st2.
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
        change (ConfRel.P4A.find) with P4A.find.
        erewrite P4A.assign_find; auto; typeclasses eauto.
      + destruct h as [hsize].
        autorewrite with interp_bit_expr in *.
        destruct a0; try easy.
        simpl.
        now rewrite P4A.find_not_first by congruence.
    - reflexivity.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      eapply JMeq_sym.
      eapply JMeq_trans.
      eapply beslice_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H).
      match goal with
      | |- n_tuple_slice hi lo ?x ~= n_tuple_slice hi lo ?y =>
        set (iu := x);
          set (ss := y);
          cut (iu ~= ss);
          try solve [apply slice_proper|apply JMeq_sym; eauto]
      end.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      eapply JMeq_sym.
      eapply JMeq_trans.
      eapply beconcat_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H).
      match goal with
      | |- n_tuple_concat ?xs1 ?ys1 ~= n_tuple_concat ?xs2 ?ys2 =>
          cut (xs1 ~= xs2 /\ ys1 ~= ys2);
          [|split]
      end.
      + intros [? ?].
        eapply concat_proper; eauto.
      + eauto using JMeq_sym.
      + eauto using JMeq_sym.
  Qed.

  Lemma be_subst_hdr_right:
    forall c (valu: bval c) (hdr: Hdr) exp phi
      st1
      bs1
      (buf1: Ntuple.n_tuple bool bs1)
      st2
      bs2
      (buf2: Ntuple.n_tuple bool bs2)
      (w: Ntuple.n_tuple bool (Hdr_sz hdr)),
      interp_bit_expr exp valu buf1 buf2 st1 st2 ~= w ->
      interp_bit_expr (a:=a) phi valu
                      buf1
                      buf2
                      st1
                      (P4A.assign _ Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)
      ~=
      interp_bit_expr (WP.be_subst phi exp (BEHdr c Right (P4A.HRVar hdr)))
                      valu
                      buf1
                      buf2
                      st1
                      st2.
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
        change (ConfRel.P4A.find) with P4A.find.
        erewrite P4A.assign_find; auto.
      + destruct h as [hsize].
        autorewrite with interp_bit_expr in *.
        destruct a0; try easy.
        simpl.
        now rewrite P4A.find_not_first by congruence.
    - reflexivity.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      eapply JMeq_sym.
      eapply JMeq_trans.
      eapply beslice_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H).
      match goal with
      | |- n_tuple_slice hi lo ?x ~= n_tuple_slice hi lo ?y =>
        set (iu := x);
          set (ss := y);
          cut (iu ~= ss);
          try solve [apply slice_proper|apply JMeq_sym; eauto]
      end.
    - subst.
      autorewrite with interp_bit_expr.
      simpl.
      eapply JMeq_sym.
      eapply JMeq_trans.
      apply beconcat_interp.
      autorewrite with interp_bit_expr.
      pose proof (inv_jmeq_size _ _ _ _ H).
      match goal with
      | |- n_tuple_concat ?xs1 ?ys1 ~= n_tuple_concat ?xs2 ?ys2 =>
          cut (xs1 ~= xs2 /\ ys1 ~= ys2);
          [|split]
      end.
      + intros [? ?].
        eapply concat_proper; eauto.
      + eauto using JMeq_sym.
      + eauto using JMeq_sym.
  Qed.

  Lemma sr_subst_hdr_left:
    forall c (valu: bval c) (hdr: Hdr) exp phi
      st1
      bs1
      (buf1: n_tuple bool bs1)
      st2
      bs2
      (buf2: n_tuple bool bs2)
      (w: Ntuple.n_tuple bool (Hdr_sz hdr)),
      w ~= interp_bit_expr exp valu buf1 buf2 st1 st2 ->
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEHdr c Left (P4A.HRVar hdr)))
        valu
        buf1
        buf2
        st1
        st2
      <->
      interp_store_rel
        (a:=a)
        phi
        valu
        buf1
        buf2
        (P4A.assign _ Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1)
        st2.
  Proof.
    induction phi;
      simpl in *;
      erewrite <- ?brand_corr, <- ?bror_corr, <- ?brimpl_corr in *;
      repeat match goal with
             | |- forall _, _ => intro
             | |- _ /\ _ => split
             | |- _ <-> _ => split
             | Hdr: _ /\ _ |- _ => destruct Hdr
             | Hdr: _ <-> _ |- _ => destruct Hdr
             | |- _ => progress subst
             | |- _ => progress autorewrite with interp_store_rel in *
             | |- _ => progress simpl in *
             | |- _ => progress erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *
             end.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - revert H0.
      assert (be_size Hdr_sz bs1 bs2 exp = Hdr_sz hdr).
      {
        eapply n_tuple_inj.
        now inversion H.
      }
      assert (Hsize1: be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr)))
              = be_size Hdr_sz bs1 bs2 e1).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      assert (Hsize2: be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr)))
              = be_size Hdr_sz bs1 bs2 e2).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      revert Hsize2 Hsize1.
      assert (Heq1: interp_bit_expr (a:=a) e1 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2 ~=
                                    interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2)
        by now apply be_subst_hdr_left.
      assert (Heq2: interp_bit_expr (a:=a) e2 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2
                              ~=
                              interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2)
        by now apply be_subst_hdr_left.
      revert Heq1 Heq2.
      generalize (interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr)))).
      generalize (interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr)))).
      intros.
      revert Heq1 Heq2.
      revert H1.
      generalize (interp_bit_expr (a:=a) e1 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2).
      generalize (interp_bit_expr (a:=a) e2 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2).
      revert Hsize2 Hsize1.
      generalize (be_size Hdr_sz bs1 bs2 e1).
      generalize (be_size Hdr_sz bs1 bs2 e2).
      intros.
      subst.
      now destruct (Classes.eq_dec n4 n3).
    - revert H0.
      assert (be_size Hdr_sz bs1 bs2 exp = Hdr_sz hdr).
      {
        eapply n_tuple_inj.
        now inversion H.
      }
      assert (Hsize1: be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e1).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      assert (Hsize2: be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e2).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      revert Hsize2 Hsize1.
      assert (Heq1: interp_bit_expr e1 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2
                              ~=
                              interp_bit_expr (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2
                              st1 st2)
        by now apply be_subst_hdr_left.
      assert (Heq2: interp_bit_expr e2 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2
                              ~=
                              interp_bit_expr (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2
                              st1 st2)
        by now apply be_subst_hdr_left.
      revert Heq1 Heq2.
      generalize (interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Left (P4A.HRVar hdr)))).
      generalize (interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Left (P4A.HRVar hdr)))).
      intros.
      revert Heq1 Heq2.
      revert H1.
      generalize (interp_bit_expr (a:=a) e1 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2).
      generalize (interp_bit_expr (a:=a) e2 valu buf1 buf2 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st1) st2).
      revert Hsize2 Hsize1.
      generalize (be_size Hdr_sz bs1 bs2 e1).
      generalize (be_size Hdr_sz bs1 bs2 e2).
      intros.
      subst.
      now destruct (Classes.eq_dec n4 n3).
    - rewrite <- brand_corr in *.
      admit.
      (* TODO Coq 8.15*)
      (* try solve [erewrite !be_subst_hdr_left in *; eauto|intuition]. *)
    - rewrite <- brand_corr in *.
      admit.
      (* try solve [erewrite !be_subst_hdr_left in *; eauto|intuition]. *)
    - rewrite <- brand_corr in *.
      autorewrite with interp_store_rel; intuition.
    - rewrite <- bror_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- bror_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- brimpl_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- brimpl_corr in *.
      autorewrite with interp_store_rel in *; intuition.
  Admitted.

  Lemma sr_subst_hdr_right:
    forall c (valu: bval c) (hdr: Hdr) exp phi
      st1
      bs1
      (buf1: n_tuple bool bs1)
      st2
      bs2
      (buf2: n_tuple bool bs2)
      (w: Ntuple.n_tuple bool (Hdr_sz hdr)),
      w ~= interp_bit_expr exp valu buf1 buf2 st1 st2 ->
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEHdr c Right (P4A.HRVar hdr)))
        valu
        buf1
        buf2
        st1
        st2
      <->
      interp_store_rel
        (a:=a)
        phi
        valu
        buf1
        buf2
        st1
        (P4A.assign _ Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2).
  Proof.
    induction phi;
      simpl in *;
      erewrite <- ?brand_corr, <- ?bror_corr, <- ?brimpl_corr in *;
      repeat match goal with
             | |- forall _, _ => intro
             | |- _ /\ _ => split
             | |- _ <-> _ => split
             | Hdr: _ /\ _ |- _ => destruct Hdr
             | Hdr: _ <-> _ |- _ => destruct Hdr
             | |- _ => progress subst
             | |- _ => progress autorewrite with interp_store_rel in *
             | |- _ => progress simpl in *
             | |- _ => progress erewrite ?brand_interp, ?bror_interp, ?brimpl_interp in *
             end.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - revert H0.
      assert (be_size Hdr_sz bs1 bs2 exp = Hdr_sz hdr).
      {
        eapply n_tuple_inj.
        now inversion H.
      }
      assert (Hsize1: be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e1).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      assert (Hsize2: be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e2).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      revert Hsize2 Hsize1.
      assert (Heq1: interp_bit_expr (a:=a) e1 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2) ~=
                                    interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2)
        by now apply be_subst_hdr_right.
      assert (Heq2: interp_bit_expr (a:=a) e2 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)
                              ~=
                              interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2)
        by now apply be_subst_hdr_right.
      revert Heq1 Heq2.
      generalize (interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr)))).
      generalize (interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr)))).
      intros.
      revert Heq1 Heq2.
      revert H1.
      generalize (interp_bit_expr (a:=a) e1 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)).
      generalize (interp_bit_expr (a:=a) e2 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)).
      revert Hsize2 Hsize1.
      generalize (be_size Hdr_sz bs1 bs2 e1).
      generalize (be_size Hdr_sz bs1 bs2 e2).
      intros.
      subst.
      now destruct (Classes.eq_dec n4 n3).
    - revert H0.
      assert (be_size Hdr_sz bs1 bs2 exp = Hdr_sz hdr).
      {
        eapply n_tuple_inj.
        now inversion H.
      }
      assert (Hsize1: be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e1).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      assert (Hsize2: be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) = be_size Hdr_sz bs1 bs2 e2).
      {
        rewrite <- !be_subst_be_size; auto.
      }
      revert Hsize2 Hsize1.
      assert (Heq1: interp_bit_expr e1 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)
                              ~=
                              interp_bit_expr (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2
                              st1 st2)
        by now apply be_subst_hdr_right.
      assert (Heq2: interp_bit_expr e2 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)
                              ~=
                              interp_bit_expr (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2
                              st1 st2)
        by now apply be_subst_hdr_right.
      revert Heq1 Heq2.
      generalize (interp_bit_expr (a:=a) (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e1 exp (BEHdr c Right (P4A.HRVar hdr)))).
      generalize (interp_bit_expr (a:=a) (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr))) valu buf1 buf2 st1 st2).
      generalize (be_size Hdr_sz bs1 bs2 (be_subst e2 exp (BEHdr c Right (P4A.HRVar hdr)))).
      intros.
      revert Heq1 Heq2.
      revert H1.
      generalize (interp_bit_expr (a:=a) e1 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)).
      generalize (interp_bit_expr (a:=a) e2 valu buf1 buf2 st1 (P4A.assign Hdr Hdr_sz hdr (P4A.VBits (Hdr_sz hdr) w) st2)).
      revert Hsize2 Hsize1.
      generalize (be_size Hdr_sz bs1 bs2 e1).
      generalize (be_size Hdr_sz bs1 bs2 e2).
      intros.
      subst.
      now destruct (Classes.eq_dec n4 n3).
    - rewrite <- brand_corr in *.
      admit.
      (* try solve [erewrite !be_subst_hdr_right in *; eauto|intuition]. *)
    - rewrite <- brand_corr in *.
      admit.
      (* try solve [erewrite !be_subst_hdr_right in *; eauto|intuition]. *)
    - rewrite <- brand_corr in *.
      autorewrite with interp_store_rel; intuition.
    - rewrite <- bror_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- bror_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- brimpl_corr in *.
      autorewrite with interp_store_rel in *; intuition.
    - rewrite <- brimpl_corr in *.
      autorewrite with interp_store_rel in *; intuition.
  Admitted.

  Lemma be_subst_buf:
    forall si c phi exp store1 store2 len1 len2 (buf1: n_tuple bool len1) (buf2: n_tuple bool len2) valu b1 b2 (w1: n_tuple bool b1) (w2: n_tuple bool b2),
        pick si (interp_bit_expr exp valu buf1 buf2 store1 store2 ~= w1,
                 interp_bit_expr exp valu buf1 buf2 store1 store2 ~= w2) ->
        pick_dep si (interp_bit_expr (a:=a) phi valu
                                     w1
                                     buf2
                                     store1
                                     store2,
                     interp_bit_expr (a:=a) phi valu
                                     buf1
                                          w2
                                          store1
                                          store2)
        ~=
        interp_bit_expr (WP.be_subst phi exp (BEBuf Hdr c si))
                      valu
                      buf1
                      buf2
                      store1
                      store2.
  Proof.
    intros si.
    induction phi; simpl in *; intros.
    - destruct si; reflexivity.
    - destruct si, a0; simpl in *;
        autorewrite with interp_bit_expr; auto.
    - destruct si; reflexivity.
    - destruct si; reflexivity.
    - apply JMeq_sym.
      eapply JMeq_trans.
      apply beslice_interp.
      destruct si;
        simpl in *;
        autorewrite with interp_bit_expr in *;
        apply slice_proper;
        eauto using JMeq_sym.
    - apply JMeq_sym.
      eapply JMeq_trans.
      apply beconcat_interp.
      destruct si;
        simpl in *;
        autorewrite with interp_bit_expr in *;
        apply concat_proper;
        eauto using JMeq_sym.
  Qed.

  Lemma sr_subst_buf:
    forall c si exp valu phi store1 store2 len1 len2 (buf1: n_tuple bool len1) (buf2: n_tuple bool len2) b1 b2 (w1: n_tuple bool b1) (w2: n_tuple bool b2),
      pick si (interp_bit_expr exp valu buf1 buf2 store1 store2 ~= w1,
               interp_bit_expr exp valu buf1 buf2 store1 store2 ~= w2) ->
      interp_store_rel
        (a:=a)
        (WP.sr_subst phi exp (BEBuf Hdr c si))
        valu
        buf1
        buf2
        store1
        store2
      <->
      pick si (interp_store_rel
                 (a:=a)
                 phi
                 valu
                 w1
                 buf2
                 store1
                 store2,
               interp_store_rel
                 (a:=a)
                 phi
                 valu
                 buf1
                 w2
                 store1
                 store2).
  Proof.
    induction phi; simpl in *; intros;
      rewrite <- ?brand_corr, <- ?bror_corr, <- ?brimpl_corr;
      autorewrite with interp_store_rel.
    - destruct si; tauto.
    - destruct si; tauto.
    - pose proof (He1 := be_subst_buf si c e1 exp store1 store2 len1 len2 buf1 buf2 valu _ _ w1 w2 ltac:(eauto)).
      pose proof (He2 := be_subst_buf si c e2 exp store1 store2 len1 len2 buf1 buf2 valu _ _ w1 w2 ltac:(eauto)).
      assert (Hsize1:
                @eq Type
                    (pick si
                           (n_tuple bool (be_size Hdr_sz b1 len2 e1),
                            n_tuple bool (be_size Hdr_sz len1 b2 e1)))
                    (n_tuple bool
                             (be_size Hdr_sz len1 len2
                                      (be_subst e1 exp (BEBuf Hdr c si)))))
        by (inversion He1; eauto).
      assert (Hsize2:
                @eq Type
                    (pick si
                          (n_tuple bool (be_size Hdr_sz b1 len2 e2),
                           n_tuple bool (be_size Hdr_sz len1 b2 e2)))
                    (n_tuple bool
                             (be_size Hdr_sz len1 len2
                                      (be_subst e2 exp (BEBuf Hdr c si)))))
        by (inversion He2; auto).
      revert He1 He2 Hsize1 Hsize2.
      repeat match goal with
             | |- context[interp_bit_expr ?e ?v ?b1 ?b2 ?st1 ?st2] =>
               generalize (interp_bit_expr (a:=a) e v b1 b2 st1 st2)
             | |- context[be_size Hdr_sz ?b1 ?b2 ?e] =>
               generalize (be_size Hdr_sz b1 b2 e)
             end.
      intros.
      destruct si; simpl in *;
        apply n_tuple_inj in Hsize1;
        apply n_tuple_inj in Hsize2;
        subst.
      + destruct (Classes.eq_dec _ _); subst; simpl.
        * intuition.
        * tauto.
      + destruct (Classes.eq_dec n1 n4); subst; simpl.
        * intuition.
        * tauto.
    - rewrite IHphi1 by eauto.
      rewrite IHphi2 by eauto.
      destruct si; reflexivity.
    - rewrite IHphi1 by eauto.
      rewrite IHphi2 by eauto.
      destruct si; reflexivity.
    - rewrite IHphi1 by eauto.
      rewrite IHphi2 by eauto.
      destruct si; reflexivity.
  Qed.

  Lemma wp_op'_size:
    forall (c: bctx) si (o: P4A.op Hdr_sz) n phi m phi',
      WP.wp_op' (c:=c) si o (P4A.op_size o + n, phi) = (m, phi') ->
      m = n.
  Proof.
    induction o; cbn; intros.
    - congruence.
    - destruct (WP.wp_op' si o2 (P4A.op_size o1 + P4A.op_size o2 + n, phi)) eqn:?.
      replace (P4A.op_size o1 + P4A.op_size o2 + n)
        with (P4A.op_size o2 + (P4A.op_size o1 + n))
        in *
        by Lia.lia.
      apply IHo2 in Heqp.
      subst n0.
      apply IHo1 in H.
      eauto.
    - replace (Hdr_sz hdr + n - Hdr_sz hdr) with n in * by Lia.lia.
      congruence.
    - congruence.
  Qed.

  Lemma wp_op'_seq:
    forall (c: bctx) (o1: P4A.op Hdr_sz) (o2: P4A.op Hdr_sz) si phi,
      WP.wp_op' (c:=c) si (P4A.OpSeq o1 o2) phi = WP.wp_op' si o1 (WP.wp_op' si o2 phi).
  Proof.
    induction o1; intros; simpl;
      repeat match goal with
             | Hdr:context [match ?x with _ => _ end] |- _ => destruct x eqn:?; simpl
             | |- context [match ?x with _ => _ end] => destruct x eqn:?; simpl
             | Hdr: (_, _) = (_, _) |- _ => inversion Hdr; clear Hdr; subst
             end;
      reflexivity.
  Qed.

  Lemma wp_op'_mono:
    forall (c: bctx) si (o: P4A.op Hdr_sz) n phi,
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

  Lemma v_inj:
    forall k j,
      @eq Type (P4A.v k) (P4A.v j) ->
      k = j.
  Proof.
    intros.
    destruct (PeanoNat.Nat.eq_dec k j); auto.
    exfalso.
    pose proof (TypeNeq.card_neq (P4A.v k) (P4A.v j)) as Hneq.
    unfold card in *.
    simpl in *.
    apply Hneq; auto.
    rewrite !map_length.
    rewrite !length_enum_tuples.
    intro.
    apply n.
    eapply PeanoNat.Nat.pow_inj_r; eauto.
  Qed.

  Lemma interp_store_rel_congr:
    forall c phi valu len1 len1'
      (buf1: n_tuple bool len1)
      (buf1': n_tuple bool len1')
      len2 len2'
      (buf2: n_tuple bool len2)
      (buf2': n_tuple bool len2')
      st1 st1' st2 st2',
      buf1 ~= buf1' ->
      buf2 ~= buf2' ->
      st1 = st1' ->
      st2 = st2' ->
      interp_store_rel (a:=a) (c:=c) phi valu buf1 buf2 st1 st2 <->
      interp_store_rel (a:=a) (c:=c) phi valu buf1' buf2' st1' st2'.
  Proof.
    intros.
    assert (len1 = len1').
    {
      inversion H.
      apply n_tuple_inj.
      auto.
    }
    assert (len2 = len2').
    {
      inversion H0.
      apply n_tuple_inj.
      auto.
    }
    subst len1'.
    subst len2'.
    rewrite H, H0, H1, H2.
    reflexivity.
  Qed.

  Lemma interp_bit_expr_congr_buf1:
    forall c (e: bit_expr Hdr c) valu l1 l1' l2 (buf1: n_tuple bool l1) (buf1': n_tuple bool l1') (buf2: n_tuple bool l2) st1 st2,
      buf1 ~= buf1' ->
      interp_bit_expr (a:=a) e valu buf1 buf2 st1 st2 ~=
      interp_bit_expr (a:=a) e valu buf1' buf2 st1 st2.
  Proof.
    intros.
    inversion H.
    apply n_tuple_inj in H2.
    subst l1'.
    rewrite H.
    reflexivity.
  Qed.

  Lemma vbits_congr:
    forall n n' (v: n_tuple bool n) (v': n_tuple bool n'),
      v ~= v' ->
      P4A.VBits n v ~= P4A.VBits n' v'.
  Proof.
    intros.
    inversion H.
    apply n_tuple_inj in H2.
    subst n'.
    rewrite H.
    reflexivity.
  Qed.

  Lemma vbits_inv:
    forall n n' (v: n_tuple bool n) (v': n_tuple bool n'),
      P4A.VBits n v ~= P4A.VBits n' v' ->
      v ~= v'.
  Proof.
    intros.
    inversion H.
    apply v_inj in H2.
    subst n'.
    apply JMeq_eq in H.
    now inversion H.
  Qed.

  Lemma n_tuple_concat_congr:
    forall n1 n1' (v1: n_tuple bool n1) (v1': n_tuple bool n1')
      n2 n2' (v2: n_tuple bool n2) (v2': n_tuple bool n2'),
      v1 ~= v1' ->
      v2 ~= v2' ->
      n_tuple_concat v1 v2 ~= n_tuple_concat v1' v2'.
  Proof.
    intros.
    inversion H.
    inversion H0.
    assert (n1 = n1') by eauto using n_tuple_inj.
    assert (n2 = n2') by eauto using n_tuple_inj.
    subst.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma expr_to_bit_expr_sound:
    forall (c: bctx) si (valu: bval c) n (expr: P4A.expr Hdr_sz n)
      bs1
      (buf1: n_tuple bool bs1)
      st1
      bs2
      (buf2: n_tuple bool bs2)
      st2,
      P4A.eval_expr Hdr Hdr_sz n (pick si (st1, st2)) expr ~=
      P4A.VBits _ (interp_bit_expr (a:=a) (WP.expr_to_bit_expr si expr) valu buf1 buf2 st1 st2).
  Proof.
    assert (Hv: forall n v, P4A.VBits n (match v with P4A.VBits _ v' => v' end) = v).
    {
      intros.
      destruct v; reflexivity.
    }
    induction expr; intros.
    - cbn.
      autorewrite with eval_expr interp_bit_expr in *.
      rewrite !Hv.
      destruct si; cbn; auto.
    - cbn.
      autorewrite with eval_expr interp_bit_expr in *.
      assert (l2t (t2l bs) ~= bs) by apply l2t_t2l.
      assert (length (t2l bs) = n) by apply t2l_len.
      revert H0.
      revert H.
      generalize (l2t (t2l bs)).
      generalize (length (t2l bs)).
      intros.
      subst.
      rewrite H.
      reflexivity.
    - simpl (expr_to_bit_expr _ _).
      autorewrite with eval_expr interp_bit_expr in *.
      assert (P4A.eval_expr Hdr Hdr_sz n (pick si (st1, st2)) expr ~=
           P4A.VBits
             (be_size Hdr_sz bs1 bs2 (expr_to_bit_expr si expr))
             (interp_bit_expr (expr_to_bit_expr si expr) valu buf1 buf2 st1 st2))
        by auto.
      destruct (P4A.eval_expr Hdr Hdr_sz n (pick si (st1, st2)) expr) eqn:?.
      rename n0 into val_e.
      generalize dependent val_e.
      generalize (interp_bit_expr (a:=a) (expr_to_bit_expr si expr) valu
                                  buf1 buf2 st1 st2)
        as val.
      simpl be_size.
      generalize (@be_size Hdr Hdr_sz c bs1 bs2 (expr_to_bit_expr si expr)) as m.
      intros m.
      change (match m with
              | 0 => 0
              | S m' => S (Nat.min hi m')
              end - lo)
        with (Nat.min (1 + hi) m - lo).
      intros.
      inversion H.
      apply v_inj in H2.
      subst n.
      apply JMeq_eq in H.
      inversion H.
      subst.
      reflexivity.
    - autorewrite with eval_expr in *.
      autorewrite with interp_bit_expr in *.
      destruct (P4A.eval_expr Hdr Hdr_sz n (pick si (st1, st2)) expr1) eqn:?.
      destruct (P4A.eval_expr Hdr Hdr_sz m (pick si (st1, st2)) expr2) eqn:?.
      simpl.
      eapply vbits_congr.
      autorewrite with interp_bit_expr.
      eapply n_tuple_concat_congr.
      + eapply vbits_inv.
        rewrite <- Heqv.
        eapply IHexpr1.
      + eapply vbits_inv.
        rewrite <- Heqv0.
        eapply IHexpr2.
  Qed.

  Lemma n_tuple_skip_n_congr:
    forall n l1 l2 (x: n_tuple bool l1) (y: n_tuple bool l2),
      x ~= y ->
      n_tuple_skip_n n x ~= n_tuple_skip_n n y.
  Proof.
    intros.
    inversion H.
    apply n_tuple_inj in H2.
    subst l2.
    apply JMeq_eq in H.
    subst.
    reflexivity.
  Qed.

  Lemma n_tuple_take_all:
    forall n (x: n_tuple bool n),
      n_tuple_take_n n x ~= x.
  Proof.
    intros.
    unfold n_tuple_take_n.
    eapply JMeq_trans.
    - eapply rewrite_size_jmeq.
    - assert (n = length (t2l x)) by eauto using t2l_len.
      Unset Printing All.
      eapply JMeq_trans; [|eapply l2t_t2l].
      revert H.
      generalize (t2l x).
      intros; subst.
      rewrite firstn_all.
      reflexivity.
  Qed.

  Lemma eval_op_congr':
    forall (st: P4A.store Hdr Hdr_sz)
      (op: P4A.op Hdr_sz)
      (buf: n_tuple bool (P4A.op_size op))
      st'
      (op': P4A.op Hdr_sz)
      (buf': n_tuple bool (P4A.op_size op')),
      st = st' ->
      buf ~= buf' ->
      op ~= op' ->
      P4A.eval_op Hdr Hdr_sz st op buf = P4A.eval_op Hdr Hdr_sz st' op' buf'.
  Proof.
    intros.
    subst.
    now apply JMeq_congr.
  Qed.

  Lemma eval_op_congr:
    forall (st: P4A.store Hdr Hdr_sz)
      (op: P4A.op Hdr_sz)
      (buf: n_tuple bool (P4A.op_size op))
      st'
      (op': P4A.op Hdr_sz)
      (buf': n_tuple bool (P4A.op_size op')),
      st = st' ->
      buf ~= buf' ->
      op ~= op' ->
      P4A.eval_op Hdr Hdr_sz st op buf ~= P4A.eval_op Hdr Hdr_sz st' op' buf'.
  Proof.
    intros.
    erewrite eval_op_congr' by eauto.
    reflexivity.
  Qed.

  Lemma wp_op'_spec_l:
    forall c (valu: bval c) (o: P4A.op Hdr_sz) n m phi st1
      (buf1: n_tuple bool (n + P4A.op_size o + m)) (buf1': n_tuple bool (P4A.op_size o)) len2 (buf2: n_tuple bool len2) st2,
      buf1' ~= n_tuple_take_n (P4A.op_size o) (n_tuple_skip_n n buf1) ->
      interp_store_rel (a:=a)
                       (snd (WP.wp_op' Left o (n + P4A.op_size o, phi)))
                       valu
                       buf1
                       buf2
                       st1
                       st2
      <->
      interp_store_rel (a:=a)
                       phi
                       valu
                       buf1
                       buf2
                       (P4A.eval_op _ _ st1 o buf1')
                       st2.
  Proof.
    induction o.
    - intros.
      autorewrite with eval_op.
      simpl.
      subst.
      reflexivity.
    - intros.
      rewrite wp_op'_seq.
      destruct (wp_op' Left o2 _) as [n' phi'] eqn:?.
      simpl in Heqp.
      replace (n + (P4A.op_size o1 + P4A.op_size o2)) with (P4A.op_size o2 + (n + P4A.op_size o1))
        in Heqp by Lia.lia.
      pose proof Heqp as Hn'.
      apply wp_op'_size in Hn'.
      subst n'.
      assert (Hsz1: n + P4A.op_size o1 + (P4A.op_size o2 + m) = n + (P4A.op_size o1 + P4A.op_size o2) + m)
        by Lia.lia.
      pose (rewrite_size Hsz1 buf1) as ibuf1.
      assert (Hsz1': P4A.op_size o1 = Nat.min (P4A.op_size o1) (n + P4A.op_size o1 + (P4A.op_size o2 + m) - n))
        by Lia.lia.
      pose (rewrite_size Hsz1' (n_tuple_take_n (P4A.op_size o1) (n_tuple_skip_n n ibuf1))) as ibuf1'.
      assert (Hibuf1': ibuf1' ~= n_tuple_take_n (P4A.op_size o1) (n_tuple_skip_n n ibuf1))
        by apply rewrite_size_jmeq.
      pose proof (IHo1 _ _ phi' st1 ibuf1 ibuf1' _ buf2 st2) as IHo1'.
      eapply iff_trans.
      eapply interp_store_rel_congr with (buf1' := ibuf1);
        eauto using rewrite_size_jmeq.
      rewrite IHo1'.
      autorewrite with eval_op.
      unfold P4A.op_size.
      set (st1' := @ConfRel.P4A.eval_op Hdr equiv1 Hdr_eq_dec Hdr_finite Hdr_sz st1 o1
          (@rewrite_size bool (Nat.min (P4A.op_size o1) (P4A.op_size o1 + P4A.op_size o2)) (P4A.op_size o1)
             (ConfRel.P4A.eval_op_obligations_obligation_1 Hdr Hdr_sz o1 o2)
             (@n_tuple_take_n bool (P4A.op_size o1 + P4A.op_size o2) (P4A.op_size o1) buf1'))).
      assert (Hsz2: n + P4A.op_size o1 + P4A.op_size o2 + m = n + (P4A.op_size o1 + P4A.op_size o2) + m) by Lia.lia.
      pose (ibuf2 := rewrite_size Hsz2 buf1).
      assert (Hsz2': P4A.op_size o2 = Nat.min (P4A.op_size o2) (n + P4A.op_size o1 + P4A.op_size o2 + m - (n + P4A.op_size o1))) by Lia.lia.
      pose (ibuf2' := rewrite_size Hsz2' (n_tuple_take_n (P4A.op_size o2) (n_tuple_skip_n (n + P4A.op_size o1) ibuf2))).
      assert (Hibuf2': ibuf2' ~= n_tuple_take_n (P4A.op_size o2) (n_tuple_skip_n (n + P4A.op_size o1) ibuf2))
        by apply rewrite_size_jmeq.
      pose proof (IHo2 (n + P4A.op_size o1) m phi st1' ibuf2 ibuf2' _ buf2 st2) as IHo2'.
      replace (P4A.op_size o2 + (n + P4A.op_size o1))
        with (n + P4A.op_size o1 + P4A.op_size o2)
        in Heqp by Lia.lia.
      rewrite Heqp in IHo2'.
      assert (Hst1': st1' = ConfRel.P4A.eval_op Hdr Hdr_sz st1 o1 ibuf1').
      {
        unfold st1'.
        change (ConfRel.P4A.eval_op) with P4A.eval_op.
        eapply eval_op_congr'; eauto.
        unfold ibuf1', ibuf1.
        eapply JMeq_trans.
        eapply rewrite_size_jmeq.
        eapply JMeq_trans;
          [|eapply JMeq_sym;
            now eapply rewrite_size_jmeq].
        apply t2l_eq.
        rewrite !t2l_n_tuple_take_n.
        rewrite t2l_n_tuple_skip_n.
        apply t2l_proper in H.
        simpl P4A.op_size in H.
        rewrite H.
        rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
        erewrite t2l_proper with (xs := rewrite_size Hsz1 buf1);
          eauto using rewrite_size_jmeq.
        rewrite firstn_firstn.
        replace (Nat.min (P4A.op_size o1) (P4A.op_size o1 + P4A.op_size o2)) with (P4A.op_size o1) by Lia.lia.
        reflexivity.
      }
      assert (Hibufs: ibuf1 ~= ibuf2)
        by eauto using JMeq_trans, rewrite_size_jmeq.
      eapply iff_trans.
      eapply interp_store_rel_congr; try eapply Hibufs; eauto.
      rewrite Hst1' in IHo2'.
      simpl in IHo2'.
      rewrite IHo2'.
      eapply interp_store_rel_congr; eauto.
      + eauto using rewrite_size_jmeq.
      + eapply eval_op_congr'; eauto.
        unfold ibuf2'.
        eapply JMeq_trans.
        eapply rewrite_size_jmeq.
        eapply JMeq_trans;
          [|eapply JMeq_sym;
            eapply rewrite_size_jmeq].
        apply t2l_eq.
        eapply eq_trans
          with (y := skipn (P4A.op_size o1) (t2l (n_tuple_take_n (P4A.op_size o1 + P4A.op_size o2) (n_tuple_skip_n n buf1)))).
        * rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          unfold ibuf2.
          replace (t2l (rewrite_size Hsz2 buf1)) with (t2l buf1)
            by (apply eq_t2l; eauto using rewrite_size_jmeq).
          rewrite <- firstn_skipn_comm.
          rewrite skipn_skipn.
          rewrite Plus.plus_comm.
          reflexivity.
        * rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          simpl in buf1'.
          simpl P4A.op_size in H.
          fold (P4A.op_size o1).
          fold (P4A.op_size o2).
          rewrite (t2l_proper _ _ _ _ H).
          rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          reflexivity.
      + apply Hibuf2'.
      + apply Hibuf1'.
    - simpl.
      intros.
      autorewrite with eval_op.
      change ConfRel.P4A.HRVar with P4A.HRVar.
      simpl in *.
      rewrite sr_subst_hdr_left with (w:=buf1'); eauto.
      reflexivity.
      autorewrite with interp_bit_expr.
      unfold n_tuple_slice.
      replace (n + Hdr_sz hdr - Hdr_sz hdr) with n by Lia.lia.
      eapply JMeq_trans;
        [eapply H|].
      apply JMeq_trans
        with (y := n_tuple_skip_n n (n_tuple_take_n (n + Hdr_sz hdr) buf1)).
      + apply t2l_eq.
        rewrite ?t2l_n_tuple_take_n, ?t2l_n_tuple_skip_n.
        rewrite firstn_skipn_comm.
        rewrite ?t2l_n_tuple_take_n, ?t2l_n_tuple_skip_n.
        reflexivity.
      + eapply n_tuple_skip_n_congr; auto.
        replace (1 + (n + Hdr_sz hdr - 1)) with (n + Hdr_sz hdr).
        reflexivity.
        assert (Hdr_sz hdr > 0) by (apply a).
        Lia.lia.
    - simpl.
      intros.
      pose proof (expr_to_bit_expr_sound c Left valu (Hdr_sz lhs) rhs _ buf1 st1 len2 buf2 st2).
      simpl in *.
      destruct (P4A.eval_expr Hdr Hdr_sz _ _ rhs) eqn:?.
      assert (Hdr_sz lhs = @be_size Hdr Hdr_sz c (n + 0 + m) len2 (expr_to_bit_expr Left rhs)).
      {
        inversion H0.
        apply v_inj; eauto.
      }
      assert (n0 ~= interp_bit_expr (a:=a) (expr_to_bit_expr Left rhs) valu buf1 buf2 st1 st2).
      {
        now apply vbits_inv in H0.
      }
      rewrite sr_subst_hdr_left; eauto.
      autorewrite with eval_op.
      rewrite Heqv.
      reflexivity.
  Qed.

  Lemma wp_op'_spec_r:
    forall c (valu: bval c) (o: P4A.op Hdr_sz) n m phi st2
      (buf2: n_tuple bool (n + P4A.op_size o + m)) (buf2': n_tuple bool (P4A.op_size o)) len1 (buf1: n_tuple bool len1) st1,
      buf2' ~= n_tuple_take_n (P4A.op_size o) (n_tuple_skip_n n buf2) ->
      interp_store_rel (a:=a)
                       (snd (WP.wp_op' Right o (n + P4A.op_size o, phi)))
                       valu
                       buf1
                       buf2
                       st1
                       st2
      <->
      interp_store_rel (a:=a)
                       phi
                       valu
                       buf1
                       buf2
                       st1
                       (P4A.eval_op _ _ st2 o buf2').
  Proof.
    induction o.
    - intros.
      autorewrite with eval_op.
      simpl.
      subst.
      reflexivity.
    - intros.
      rewrite wp_op'_seq.
      destruct (wp_op' Right o2 _) as [n' phi'] eqn:?.
      simpl P4A.op_size in Heqp.
      replace (n + (P4A.op_size o1 + P4A.op_size o2)) with (P4A.op_size o2 + (n + P4A.op_size o1))
        in Heqp by Lia.lia.
      pose proof Heqp as Hn'.
      apply wp_op'_size in Hn'.
      subst n'.
      assert (Hsz1: n + P4A.op_size o1 + (P4A.op_size o2 + m) = n + (P4A.op_size o1 + P4A.op_size o2) + m)
        by Lia.lia.
      pose (rewrite_size Hsz1 buf2) as ibuf1.
      assert (Hsz1': P4A.op_size o1 = Nat.min (P4A.op_size o1) (n + P4A.op_size o1 + (P4A.op_size o2 + m) - n))
        by Lia.lia.
      pose (rewrite_size Hsz1' (n_tuple_take_n (P4A.op_size o1) (n_tuple_skip_n n ibuf1))) as ibuf1'.
      assert (Hibuf1': ibuf1' ~= n_tuple_take_n (P4A.op_size o1) (n_tuple_skip_n n ibuf1))
        by apply rewrite_size_jmeq.
      pose proof (IHo1 _ _ phi' st2 ibuf1 ibuf1' _ buf1 st1)
        as IHo1'.
      eapply iff_trans.
      eapply interp_store_rel_congr with (buf2' := ibuf1);
        eauto using rewrite_size_jmeq.
      rewrite IHo1'.
      autorewrite with eval_op.
      unfold P4A.op_size.
      set (st2' := @ConfRel.P4A.eval_op Hdr equiv1 Hdr_eq_dec Hdr_finite Hdr_sz st2 o1
          (@rewrite_size bool (Nat.min (P4A.op_size o1) (P4A.op_size o1 + P4A.op_size o2)) (P4A.op_size o1)
             (ConfRel.P4A.eval_op_obligations_obligation_1 Hdr Hdr_sz o1 o2)
             (@n_tuple_take_n bool (P4A.op_size o1 + P4A.op_size o2) (P4A.op_size o1) buf2'))).
      assert (Hsz2: n + P4A.op_size o1 + P4A.op_size o2 + m = n + (P4A.op_size o1 + P4A.op_size o2) + m) by Lia.lia.
      pose (ibuf2 := rewrite_size Hsz2 buf2).
      assert (Hsz2': P4A.op_size o2 = Nat.min (P4A.op_size o2) (n + P4A.op_size o1 + P4A.op_size o2 + m - (n + P4A.op_size o1))) by Lia.lia.
      pose (ibuf2' := rewrite_size Hsz2' (n_tuple_take_n (P4A.op_size o2) (n_tuple_skip_n (n + P4A.op_size o1) ibuf2))).
      assert (Hibuf2': ibuf2' ~= n_tuple_take_n (P4A.op_size o2) (n_tuple_skip_n (n + P4A.op_size o1) ibuf2))
        by apply rewrite_size_jmeq.
      pose proof (IHo2 (n + P4A.op_size o1) m phi st2' ibuf2 ibuf2' _ buf1 st1) as IHo2'.
      replace (P4A.op_size o2 + (n + P4A.op_size o1))
        with (n + P4A.op_size o1 + P4A.op_size o2)
        in Heqp by Lia.lia.
      rewrite Heqp in IHo2'.
      assert (Hst1': st2' = ConfRel.P4A.eval_op Hdr Hdr_sz st2 o1 ibuf1').
      {
        unfold st2'.
        change (ConfRel.P4A.eval_op) with P4A.eval_op.
        eapply eval_op_congr'; eauto.
        unfold ibuf1', ibuf1.
        eapply JMeq_trans.
        eapply rewrite_size_jmeq.
        eapply JMeq_trans;
          [|eapply JMeq_sym;
            eapply rewrite_size_jmeq].
        apply t2l_eq.
        rewrite !t2l_n_tuple_take_n.
        rewrite t2l_n_tuple_skip_n.
        apply t2l_proper in H.
        simpl P4A.op_size in H.
        rewrite H.
        rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
        erewrite t2l_proper with (xs := rewrite_size Hsz1 buf2);
          eauto using rewrite_size_jmeq.
        rewrite firstn_firstn.
        replace (Nat.min (P4A.op_size o1) (P4A.op_size o1 + P4A.op_size o2)) with (P4A.op_size o1) by Lia.lia.
        reflexivity.
      }
      assert (Hibufs: ibuf1 ~= ibuf2)
        by eauto using JMeq_trans, rewrite_size_jmeq.
      eapply iff_trans.
      eapply interp_store_rel_congr; try eapply Hibufs; eauto.
      rewrite Hst1' in IHo2'.
      simpl in IHo2'.
      rewrite IHo2'.
      eapply interp_store_rel_congr; eauto.
      + eauto using rewrite_size_jmeq.
      + eapply eval_op_congr'; eauto.
        unfold ibuf2'.
        etransitivity.
        apply rewrite_size_jmeq.
        etransitivity;
          [|symmetry; apply rewrite_size_jmeq].
        apply t2l_eq.
        eapply eq_trans
          with (y := skipn (P4A.op_size o1) (t2l (n_tuple_take_n (P4A.op_size o1 + P4A.op_size o2) (n_tuple_skip_n n buf2)))).
        * rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          unfold ibuf2.
          replace (t2l (rewrite_size Hsz2 buf2)) with (t2l buf2)
            by (apply eq_t2l; eauto using rewrite_size_jmeq).
          rewrite <- firstn_skipn_comm.
          rewrite skipn_skipn.
          rewrite Plus.plus_comm.
          reflexivity.
        * rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          simpl P4A.op_size in H.
          fold (P4A.op_size o1).
          fold (P4A.op_size o2).
          rewrite (t2l_proper _ _ _ _ H).
          rewrite !t2l_n_tuple_take_n, !t2l_n_tuple_skip_n.
          reflexivity.
      + apply Hibuf2'.
      + apply Hibuf1'.
    - simpl.
      intros.
      autorewrite with eval_op.
      change ConfRel.P4A.HRVar with P4A.HRVar.
      simpl in *.
      rewrite sr_subst_hdr_right with (w:=buf2'); eauto.
      reflexivity.
      autorewrite with interp_bit_expr.
      unfold n_tuple_slice.
      replace (n + Hdr_sz hdr - Hdr_sz hdr) with n by Lia.lia.
      etransitivity.
      apply H.
      apply JMeq_trans
        with (y := n_tuple_skip_n n (n_tuple_take_n (n + Hdr_sz hdr) buf2)).
      + apply t2l_eq.
        rewrite ?t2l_n_tuple_take_n, ?t2l_n_tuple_skip_n.
        rewrite firstn_skipn_comm.
        rewrite ?t2l_n_tuple_take_n, ?t2l_n_tuple_skip_n.
        reflexivity.
      + eapply n_tuple_skip_n_congr; auto.
        assert (Hdr_sz hdr > 0) by (apply a).
        replace (1 + (n + Hdr_sz hdr - 1)) with (n + Hdr_sz hdr) by Lia.lia.
        reflexivity.
    - simpl.
      intros.
      pose proof (expr_to_bit_expr_sound c Right valu (Hdr_sz lhs) rhs _ buf1 st1 _ buf2 st2).
      simpl in *.
      destruct (P4A.eval_expr Hdr Hdr_sz (Hdr_sz lhs) _ rhs) eqn:?.
      assert (Hdr_sz lhs = @be_size Hdr Hdr_sz c len1 (n + 0 + m) (expr_to_bit_expr Right rhs)).
      {
        inversion H0.
        apply v_inj; eauto.
      }
      assert (n0 ~= interp_bit_expr (a:=a) (expr_to_bit_expr Right rhs) valu buf1 buf2 st1 st2).
      {
        now apply vbits_inv in H0.
      }
      rewrite sr_subst_hdr_right; eauto.
      autorewrite with eval_op.
      rewrite Heqv.
      reflexivity.
  Qed.

  Lemma in_interp_tpairs:
    forall ts q1 q2 t1 t2,
      In (t1, t2) ts ->
      interp_state_template t1 q1 ->
      interp_state_template t2 q2 ->
      interp_tpairs (a:=a) ts q1 q2.
  Proof.
    induction ts; intros; simpl.
    - exact H.
    - destruct a0.
      simpl in H.
      destruct H.
      + left.
        split; congruence.
      + right.
        eapply IHts; eauto.
  Qed.

  (* n.b. not sure this lemma is used anywhere yet *)
  Lemma wp_bounded:
    forall top phi phi' q1 q2,
      In phi' (wp (a:=a) top phi) ->
      interp_conf_state (cr_st phi') q1 q2 ->
      interp_tpairs top q1 q2.
  Proof.
    intros.
    unfold wp, wp_pred_pair in *.
    apply in_map_iff in H.
    destruct H as [[? [? ?]] [? ?]].
    subst phi'.
    apply in_flat_map in H1.
    destruct H1 as [[? ?] [? ?]].
    unfold interp_conf_state in H0.
    destruct H0; simpl in *.
    apply Reachability.reaches_prev in H1.
    eapply in_interp_tpairs; eauto || congruence.
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
    rewrite !H1, !H2, !H, !H3.
    destruct (conf_state q1), (conf_state q2); auto.
  Qed.

  Ltac set_jmeq var exp :=
    let Heq := fresh "Heq" in
    let Hjmeq := fresh "Hjmeq" in
    remember exp as var eqn:Heq;
    assert (Hjmeq: var ~= exp)
        by (rewrite Heq; reflexivity);
    clear Heq.

  Definition kind_leap_size (si: side) (k: lkind) (q1 q2: conf) (l: nat) : Prop :=
    match k with
    | Read =>
      l < configuration_room_left (pick si (q1, q2))
    | Jump =>
      l = configuration_room_left (pick si (q1, q2)) \/
      exists a, conf_state (pick si (q1, q2)) = inr a /\
           l >= 1
    end.

  (* Soundness of left- and right- weakest precondition operators. *)
  Lemma wp_lpred_pair_read_safe:
    forall (c: bctx) si (valu: bval c) b prev cur phi q1 q2,
      interp_store_rel (wp_lpred (a:=a) si b prev cur Read phi) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ->
      forall bs (q1' q2': conf),
        bs = t2l (interp_bvar valu b) ->
        kind_leap_size si Read q1 q2 (check_bvar b) ->
        q1' = pick si (follow q1 bs, q1) ->
        q2' = pick si (q2, follow q2 bs) ->
        interp_store_rel phi valu (conf_buf q1') (conf_buf q2') (conf_store q1') (conf_store q2').
  Proof.
    unfold wp_lpred.
    intros.
    destruct si.
    - remember (interp_bit_expr (BEConcat (BEBuf Hdr c Left) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2)) as w.
      assert (interp_bit_expr (BEConcat (BEBuf Hdr c Left) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ~= w).
      {
        rewrite Heqw.
        reflexivity.
      }
      clear Heqw.
      rewrite sr_subst_buf in H by eauto.
      simpl in *.
      subst q2' q1'.
      autorewrite with interp_store_rel interp_bit_expr in *.
      set (q1' := follow q1 bs).
      assert (conf_buf_len q1 + length bs < size' _ (conf_state q1)).
      {
          unfold configuration_room_left in *.
          subst bs.
          rewrite t2l_len in *.
          Lia.lia.
      }
      assert (Hs: conf_state q1' = conf_state q1) by eauto using conf_state_follow_fill.
      assert (Hst: conf_store q1' = conf_store q1) by eauto using conf_store_follow_fill.
      assert (Hlen: conf_buf_len q1' = (conf_buf_len q1) + (length bs)) by eauto using conf_buf_len_follow_fill.
      assert (conf_buf q1' ~= n_tuple_concat (conf_buf q1) (l2t bs)) by eauto using conf_buf_follow_fill.
      assert (Hbuf1: conf_buf q1' ~= n_tuple_concat (conf_buf q1) (interp_bvar valu b)).
      {
        subst bs.
        etransitivity.
        apply H3.
        apply concat_proper; auto.
        apply l2t_t2l.
      }
      assert (Hbuf2: conf_buf q1' ~= w).
      {
        eapply JMeq_trans; eauto.
      }
      rewrite Hst.
      subst bs.
      rewrite t2l_len in Hlen.
      revert Hbuf2.
      revert H.
      generalize (conf_buf q1').
      generalize (conf_buf_len q1').
      generalize w.
      generalize (conf_buf_len q1 + check_bvar b).
      intros.
      inversion Hbuf2.
      apply n_tuple_inj in H6.
      subst n0.
      subst n1.
      auto.
    - remember (interp_bit_expr (BEConcat (BEBuf Hdr c Right) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2)) as w.
      assert (interp_bit_expr (BEConcat (BEBuf Hdr c Right) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ~= w).
      {
        rewrite Heqw.
        reflexivity.
      }
      clear Heqw.
      rewrite sr_subst_buf in H; simpl; eauto.
      simpl in *.
      subst q2' q1'.
      autorewrite with interp_store_rel interp_bit_expr in *.
      set (q2' := follow q2 bs).
      assert (conf_buf_len q2 + length bs < size' _ (conf_state q2)).
      {
          unfold configuration_room_left in *.
          subst bs.
          rewrite t2l_len in *.
          Lia.lia.
      }
      assert (Hs: conf_state q2' = conf_state q2) by eauto using conf_state_follow_fill.
      assert (Hst: conf_store q2' = conf_store q2) by eauto using conf_store_follow_fill.
      assert (Hlen: conf_buf_len q2' = (conf_buf_len q2) + (length bs)) by eauto using conf_buf_len_follow_fill.
      assert (conf_buf q2' ~= n_tuple_concat (conf_buf q2) (l2t bs)) by eauto using conf_buf_follow_fill.
      assert (Hbuf1: conf_buf q2' ~= n_tuple_concat (conf_buf q2) (interp_bvar valu b)).
      {
        subst bs.
        etransitivity.
        eapply H3.
        apply concat_proper; auto.
        apply l2t_t2l.
      }
      assert (Hbuf2: conf_buf q2' ~= w).
      {
        eapply JMeq_trans; eauto.
      }
      rewrite Hst.
      subst bs.
      rewrite t2l_len in Hlen.
      revert Hbuf2.
      revert H.
      generalize (conf_buf q2').
      generalize (conf_buf_len q2').
      generalize w.
      generalize (conf_buf_len q2 + check_bvar b).
      intros.
      inversion Hbuf2.
      apply n_tuple_inj in H6.
      subst n0.
      subst n1.
      auto.
    Unshelve.
    exact 0.
    exact tt.
    exact 0.
    exact tt.
  Qed.

  Lemma step_done_store:
    forall (q: conf) a b,
      conf_state q = inr b ->
      conf_store (step q a) = conf_store q.
  Proof.
    unfold step.
    intros.
    destruct (Compare_dec.le_lt_dec _ _).
    - simpl.
      generalize (eq_rect (S (conf_buf_len q)) (n_tuple bool)
       (conf_buf q, a0) (size' (P4A.interp a) (conf_state q))
       (squeeze (conf_buf_sane q) l)).
      rewrite H.
      intros.
      now autorewrite with update'.
    - reflexivity.
  Qed.

  Lemma follow_done_store:
    forall (q: conf) bs b,
      conf_state q = inr b ->
      conf_store (follow q bs) = conf_store q.
  Proof.
    intros q bs.
    revert q.
    induction bs; intros; autorewrite with follow.
    - reflexivity.
    - erewrite IHbs by eauto using conf_state_step_done.
      eapply step_done_store; eauto.
  Qed.

  Lemma conf_room_nonzero:
    forall q: conf,
      configuration_room_left q > 0.
  Proof.
    destruct q.
    unfold configuration_room_left.
    simpl.
    Lia.lia.
  Qed.

  Lemma leap_size_nonzero:
    forall q1 q2: conf,
      leap_size _ q1 q2 > 0.
  Proof.
    unfold leap_size.
    intros.
    pose proof (conf_room_nonzero q1).
    pose proof (conf_room_nonzero q2).
    destruct (conf_state q1), (conf_state q2); Lia.lia.
  Qed.

  Lemma update'_congr:
    forall a s s' buf buf' st st',
      s = s' ->
      buf ~= buf' ->
      st = st' ->
      update' a s buf st =
      update' a s' buf' st'.
  Proof.
    intros.
    subst.
    reflexivity.
  Qed.

  Lemma interp_store_rel_breq_jmeq:
    forall c e1 e2 valu b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2) st1 st2,
      interp_store_rel (c:=c) (BREq e1 e2) valu buf1 buf2 st1 st2 <->
      interp_bit_expr (a:=a) e1 valu buf1 buf2 st1 st2 ~=
      interp_bit_expr e2 valu buf1 buf2 st1 st2.
  Proof.
    intros.
    autorewrite with interp_store_rel.
    destruct (eq_dec _ _).
    - intuition.
      + assert (Hr: eq_rect (be_size Hdr_sz b1 b2 e1) (n_tuple bool) (interp_bit_expr e1 valu buf1 buf2 st1 st2) (be_size Hdr_sz b1 b2 e2) e ~= interp_bit_expr e2 valu buf1 buf2 st1 st2)
          by now rewrite H.
        eapply JMeq_trans; try eapply Hr.
        clear H.
        clear Hr.
        destruct e.
        simpl.
        reflexivity.
      + apply JMeq_eq.
        destruct e.
        simpl.
        auto.
    - intuition.
      apply n.
      apply n_tuple_inj.
      now inversion H.
  Qed.

  Section PatCondInd.
    Variable (P: forall ty, P4A.cond Hdr_sz ty -> P4A.pat ty -> Prop).
    Variable (HExprExact:
                forall {n e v},
                  P (P4A.TBits n) (P4A.CExpr e) (P4A.PExact v)).
    Variable (HExprAny:
                forall {n e},
                  P (P4A.TBits n) (P4A.CExpr e) (P4A.PAny n)).
    Variable (HPair: forall {t1 t2 e1 e2 p1 p2},
                 P t1 e1 p1 ->
                 P t2 e2 p2 ->
                 P (P4A.TPair t1 t2) (P4A.CPair e1 e2) (P4A.PPair p1 p2)).
    Equations pat_cond_ind ty cond pat : P ty cond pat :=
      { pat_cond_ind (P4A.TBits n) (P4A.CExpr e) (P4A.PExact v) := HExprExact;
        pat_cond_ind (P4A.TBits n) (P4A.CExpr e) (P4A.PAny n) := HExprAny;
        pat_cond_ind (P4A.TPair t1 t2) (P4A.CPair e1 e2) (P4A.PPair p1 p2) :=
          HPair (pat_cond_ind _ e1 p1) (pat_cond_ind _ e2 p2) }.
  End PatCondInd.

  Definition pat_cond_ok ty (cond: P4A.cond Hdr_sz ty) pat :=
    forall ctx st1 st2 si (valu: bval ctx) b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2),
      P4A.match_pat Hdr Hdr_sz (pick si (st1, st2)) cond pat = true <->
      interp_store_rel (a:=a) (pat_cond si pat cond) valu buf1 buf2 st1 st2.

  Lemma val_to_bit_expr_interp:
    forall n (v: P4A.v n) ctx st1 st2 (valu: bval ctx) b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2),
      interp_bit_expr (a:=a) (val_to_bit_expr Hdr v) valu buf1 buf2 st1 st2 ~= projbits v.
  Proof.
    unfold val_to_bit_expr.
    destruct v.
    intros.
    autorewrite with interp_bit_expr.
    eapply JMeq_trans; eauto using l2t_t2l.
  Qed.

  Lemma projbits_congr:
    forall n1 n2 (v1: P4A.v n1) (v2: P4A.v n2),
      v1 ~= v2 ->
      projbits v1 ~= projbits v2.
  Proof.
    intros.
    inversion H.
    apply v_inj in H1.
    subst.
    rewrite H.
    reflexivity.
  Qed.

  Lemma pat_cond_safe:
    forall ty (cond: P4A.cond Hdr_sz ty) pat ctx st1 st2 si (valu: bval ctx) b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2),
      P4A.match_pat Hdr Hdr_sz (pick si (st1, st2)) cond pat = true <->
      interp_store_rel (a:=a) (pat_cond si pat cond) valu buf1 buf2 st1 st2.
  Proof.
    intros ty cond pat.
    fold (pat_cond_ok ty cond pat).
    eapply pat_cond_ind; intros; unfold pat_cond_ok;
      intros;
      autorewrite with match_pat pat_cond.
    - rewrite interp_store_rel_breq_jmeq.
      destruct (EquivDec.equiv_dec _ _); eauto.
      + unfold Equivalence.equiv in e0.
        subst v.
        intuition.
        set (be := expr_to_bit_expr si e).
        assert (ConfRel.P4A.eval_expr Hdr Hdr_sz n (pick si (st1, st2)) e ~=
                P4A.VBits (be_size Hdr_sz _ _ be) (interp_bit_expr (a:=a) be valu buf1 buf2 st1 st2))
          by eapply expr_to_bit_expr_sound.
        eapply JMeq_trans;
          [|symmetry; apply val_to_bit_expr_interp].
        eapply JMeq_trans;
          [|symmetry; apply projbits_congr; apply H0].
        reflexivity.
      + intuition.
        exfalso.
        apply c.
        unfold Equivalence.equiv.
        destruct v.
        eapply JMeq_eq.
        eapply JMeq_trans.
        eapply expr_to_bit_expr_sound.
        eapply vbits_congr.
        etransitivity.
        eapply H.
        replace n0 with (projbits (P4A.VBits n n0)).
        eapply val_to_bit_expr_interp.
        reflexivity.
    - autorewrite with interp_store_rel; tauto.
    - autorewrite with interp_store_rel.
      rewrite Bool.andb_true_iff.
      intuition.
  Qed.

  Lemma cases_cond_safe:
    forall ty (cond: P4A.cond Hdr_sz ty) cases default ctx st1 st2 s si (valu: bval ctx) b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2),
      P4A.eval_sel St Hdr Hdr_sz (pick si (st1, st2)) cond cases default = s ->
      interp_store_rel (a:=a) (cases_cond si cond s cases default) valu buf1 buf2 st1 st2.
  Proof.
    induction cases as [|c cases]; simpl; intros.
    - subst.
      destruct (EquivDec.equiv_dec s s);
        autorewrite with interp_store_rel;
        [tauto|congruence].
    - destruct (P4A.match_pat _ _ _ _) eqn:?.
      + destruct (EquivDec.equiv_dec _ _); [|congruence].
        rewrite <- bror_corr.
        autorewrite with interp_store_rel.
        left.
        now apply pat_cond_safe.
      + destruct (EquivDec.equiv_dec _ _).
        * rewrite <- bror_corr.
          autorewrite with interp_store_rel.
          right.
          now eapply IHcases.
        * rewrite <- brand_corr; autorewrite with interp_store_rel.
          rewrite <- brimpl_corr; autorewrite with interp_store_rel.
          split; eauto.
          intro.
          apply pat_cond_safe in H0.
          congruence.
  Qed.

  Lemma trans_cond_safe:
    forall t si c st1 st2 s (valu: bval c) b1 (buf1: n_tuple bool b1) b2 (buf2: n_tuple bool b2),
      P4A.eval_trans St Hdr Hdr_sz (pick si (st1, st2)) t = s ->
      interp_store_rel (a:=a) (trans_cond si t s) valu buf1 buf2 st1 st2.
  Proof.
    induction t; simpl; intros.
    - subst.
      destruct (EquivDec.equiv_dec s s);
        autorewrite with interp_store_rel;
        [tauto|congruence].
    - auto using cases_cond_safe.
  Qed.

  Lemma wp_lpred_pair_jump_safe:
    forall (c: bctx) si (valu: bval c) b prev cur phi q1 q2,
      interp_state_template prev (pick si (q1, q2)) ->
      interp_store_rel (wp_lpred (a:=a) si b prev cur Jump phi) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ->
      forall bs (q1' q2': conf),
        interp_state_template cur (pick si (q1', q2')) ->
        kind_leap_size si Jump q1 q2 (check_bvar b) ->
        bs = t2l (interp_bvar valu b) ->
        q1' = pick si (follow q1 bs, q1) ->
        q2' = pick si (q2, follow q2 bs) ->
        interp_store_rel phi valu (conf_buf q1') (conf_buf q2') (conf_store q1') (conf_store q2').
  Proof.
    unfold wp_lpred.
    intros.
    destruct si.
    - remember (interp_bit_expr (BEConcat (BEBuf Hdr c Left) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2)) as w.
      assert (interp_bit_expr (BEConcat (BEBuf Hdr c Left) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ~= w).
      {
        rewrite Heqw.
        reflexivity.
      }
      clear Heqw.
      rewrite sr_subst_buf in H0 by eauto.
      simpl in *.
      subst w.
      autorewrite with interp_store_rel interp_bit_expr in *.
      subst q2'.
      destruct H as [Hprevst Hprevlen].
      rewrite Hprevst in *.
      destruct (conf_state q1) eqn:Hst.
      + destruct H2 as [Hlen | [b' [Hst' Hlen]]];
          [|congruence].
        unfold wp_op in H0.
        set (o := (ConfRel.P4A.st_op (ConfRel.P4A.t_states a s))) in *.
        set (n := P4A.st_size (P4A.t_states a s)) in *.
        unfold P4A.op_size in *.
        set (phi' := brimpl (jump_cond Left prev cur)
                           (sr_subst phi (BELit Hdr c nil) (BEBuf Hdr c Left))) in *.
        change n with (0 + n) in H0.
        remember (n_tuple_concat (conf_buf q1) (interp_bvar valu b)) as buf.
        unfold configuration_room_left in Hlen.
        rewrite Hst in Hlen.
        autorewrite with size' in Hlen.
        simpl in Hlen.
        assert (Hsz': 0 + P4A.size a s + 0 = conf_buf_len q1 + check_bvar b).
        {
          rewrite Hlen.
          pose proof (conf_buf_sane q1).
          rewrite Hst in *.
          autorewrite with size' in *.
          unfold size in *.
          simpl in *.
          Lia.lia.
        }
        pose (buf' := rewrite_size Hsz' buf).
        unfold P4A.size in buf'.
        assert (Hsz'': n = Nat.min n (0 + P4A.st_size (P4A.t_states a s) + 0 - 0)).
        {
          subst n.
          simpl.
          unfold P4A.st_size.
          Lia.lia.
        }
        pose (buf'' := rewrite_size Hsz'' (n_tuple_take_n n (n_tuple_skip_n 0 buf'))).
        pose proof (wp_op'_spec_l c valu o 0 0 phi' (conf_store q1) buf' buf'' _ (conf_buf q2) (conf_store q2)) as wp_op'_spec.
        specialize (wp_op'_spec ltac:(eauto using rewrite_size_jmeq)).
        eapply interp_store_rel_congr in H0;
          [eapply wp_op'_spec in H0 | | | |];
          eauto;
          [|subst; now eauto using rewrite_size_jmeq].
        unfold phi' in H0.
        rewrite <- brimpl_corr in H0.
        autorewrite with interp_store_rel in H0.
        rewrite sr_subst_buf in H0; simpl; eauto.
        simpl in H0.
        autorewrite with interp_bit_expr in *.
        simpl (l2t nil) in *.
        assert (conf_buf_len q1 + length bs = size' (P4A.interp a) (conf_state q1)).
        {
          rewrite Hst.
          autorewrite with size'.
          unfold size; simpl.
          subst bs.
          rewrite t2l_len.
          Lia.lia.
        }
        assert (Hnil: conf_buf_len q1' = 0).
        {
          subst q1'.
          eapply conf_buf_len_follow_transition; eauto.
        }
        generalize (conf_buf q1').
        rewrite Hnil.
        intros.
        destruct n0.
        eapply interp_store_rel_congr; try eapply H0; eauto.
        * (* need lemma saying that conf_store is eval_op after a transition *)
          assert (Hfb: size' _ (conf_state q1) = conf_buf_len q1 + length bs).
          {
            rewrite Hst.
            autorewrite with size'.
            simpl.
            rewrite H3.
            rewrite t2l_len.
            rewrite Hlen.
            Lia.lia.
          }
          set (full_buf := rewrite_size Hfb (n_tuple_concat (conf_buf q1) (l2t bs))).
          assert (full_buf ~= n_tuple_concat (conf_buf q1) (l2t bs))
            by eapply rewrite_size_jmeq.
          assert (Hfb': size' _ (inl s) = size' _ (conf_state q1))
            by now rewrite Hst.
          set (full_buf' := rewrite_size Hfb' full_buf).
          assert (full_buf' ~= full_buf)
            by eapply rewrite_size_jmeq.
          subst q1'.
          erewrite conf_store_follow_transition; eauto.
          replace (update' (P4A.interp a) (conf_state q1) full_buf (conf_store q1))
            with (update' (P4A.interp a) (inl s) full_buf' (conf_store q1))
            by (apply update'_congr; eauto).
          autorewrite with update'.
          simpl.
          unfold P4A.update.
          apply eval_op_congr'; eauto.
          unfold buf''.
          destruct (plus_O_n _); simpl.
          etransitivity;
            [|symmetry; eapply rewrite_size_jmeq].
          eapply JMeq_trans with (y:=full_buf); eauto.
          unfold buf'.
          apply t2l_eq.
          rewrite t2l_n_tuple_take_n, t2l_n_tuple_skip_n.
          rewrite skipn_O.
          replace n with (length (t2l (rewrite_size Hsz' buf))).
          rewrite firstn_all.
          apply t2l_proper.
          etransitivity;
            [|symmetry; apply rewrite_size_jmeq].
          rewrite Heqbuf.
          etransitivity; try apply H2.
          apply n_tuple_concat_congr; eauto.
          rewrite H3.
          etransitivity.
          eapply l2t_t2l.
          reflexivity.
          unfold n.
          rewrite t2l_len.
          unfold P4A.size, P4A.st_size.
          Lia.lia.
        * (* need lemma saying if cur |= q1' then jump_cond is true *)
          assert (Hnz: n = conf_buf_len q1 + length bs).
          {
            subst n.
            rewrite Hst in *.
            autorewrite with size' in *.
            simpl in *.
            unfold P4A.size in *.
            unfold P4A.st_size in *.
            Lia.lia.
          }
          unfold jump_cond.
          rewrite Hprevst.
          apply trans_cond_safe.
          destruct H1.
          rewrite H1.
          rewrite H4.
          erewrite conf_state_follow_transition; eauto.
          autorewrite with transitions'; simpl.
          unfold P4A.transitions.
          change ConfRel.P4A.eval_trans with P4A.eval_trans.
          assert (Hfb: size' _ (conf_state q1) = conf_buf_len q1 + length bs).
          {
            rewrite Hst.
            autorewrite with size'.
            rewrite <- Hnz.
            unfold n.
            reflexivity.
          }
          pose (full_buf := rewrite_size Hfb (n_tuple_concat (conf_buf q1) (l2t bs))).
          erewrite conf_store_follow_transition with (full_buf := full_buf); 
          eauto using rewrite_size_jmeq.
          f_equal.
          autorewrite with update'.
          replace (update' (ConfRel.P4A.interp a) (conf_state q1) full_buf (conf_store q1))
            with (update (P4A.interp a) s buf'' (conf_store q1)).
          simpl.
          unfold P4A.update.
          eapply eval_op_congr'; eauto.
          destruct (plus_O_n _); reflexivity.
          rewrite <- update'_equation_1.
          apply update'_congr; eauto.
          unfold buf'', buf', full_buf.
          etransitivity.
          eapply rewrite_size_jmeq.
          etransitivity;
            [|symmetry; eapply rewrite_size_jmeq].
          apply t2l_eq.
          rewrite t2l_n_tuple_take_n.
          rewrite t2l_n_tuple_skip_n.
          rewrite skipn_O.
          replace n with (length (t2l (rewrite_size Hsz' buf))).
          rewrite firstn_all.
          apply eq_t2l.
          etransitivity.
          eapply rewrite_size_jmeq.
          rewrite Heqbuf.
          subst bs.
          apply n_tuple_concat_congr; eauto.
          symmetry; apply l2t_t2l.
          rewrite t2l_len.
          rewrite Hnz.
          subst bs.
          rewrite t2l_len.
          Lia.lia.
      + assert (Hbs: length bs > 0).
        {
          pose proof (conf_room_nonzero q1).
          subst bs.
          rewrite t2l_len.
          destruct H2 as [Hlen | [b' [Hst' Hlen]]];
            Lia.lia.
        }
        unfold kind_leap_size in *.
        rewrite sr_subst_buf in H0 by (simpl; eauto).
        simpl in *.
        autorewrite with interp_bit_expr in *.
        replace (conf_store q1') with (conf_store q1)
          by (symmetry;
              rewrite H4;
              eapply follow_done_store; eauto).
        set (buf' := conf_buf q1').
        pose proof (conf_buf_sane q1').
        rewrite H4 in H.
        erewrite follow_finish in H; eauto.
        autorewrite with size' in *.
        assert (conf_buf_len (follow q1 bs) = 0) by Lia.lia.
        assert (Hzero: conf_buf_len q1' = 0) by congruence.
        generalize buf'.
        clear buf'.
        rewrite Hzero.
        intros buf'.
        destruct buf'.
        auto.
    - remember (interp_bit_expr (BEConcat (BEBuf Hdr c Right) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2)) as w.
      assert (interp_bit_expr (BEConcat (BEBuf Hdr c Right) (BEVar Hdr b)) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ~= w).
      {
        rewrite Heqw.
        reflexivity.
      }
      clear Heqw.
      rewrite sr_subst_buf in H0 by eauto.
      simpl in *.
      subst w.
      autorewrite with interp_store_rel interp_bit_expr in *.
      subst q1'.
      destruct H as [Hprevst Hprevlen].
      rewrite Hprevst in *.
      destruct (conf_state q2) eqn:Hst.
      + destruct H2 as [Hlen | [b' [Hst' Hlen]]];
          [|congruence].
        unfold wp_op in H0.
        set (o := (ConfRel.P4A.st_op (ConfRel.P4A.t_states a s))) in *.
        set (n := P4A.st_size (P4A.t_states a s)) in *.
        unfold P4A.op_size in *.
        set (phi' := brimpl (jump_cond Right prev cur)
                           (sr_subst phi (BELit Hdr c nil) (BEBuf Hdr c Right))) in *.
        change n with (0 + n) in H0.
        remember (n_tuple_concat (conf_buf q2) (interp_bvar valu b)) as buf.
        unfold configuration_room_left in Hlen.
        rewrite Hst in Hlen.
        autorewrite with size' in Hlen.
        simpl in Hlen.
        assert (Hsz': 0 + P4A.size a s + 0 = conf_buf_len q2 + check_bvar b).
        {
          rewrite Hlen.
          pose proof (conf_buf_sane q2).
          rewrite Hst in *.
          autorewrite with size' in *.
          unfold size in *.
          simpl in *.
          Lia.lia.
        }
        pose (buf' := rewrite_size Hsz' buf).
        unfold P4A.size in buf'.
        assert (Hsz'': n = Nat.min n (0 + P4A.st_size (P4A.t_states a s) + 0 - 0)).
        {
          subst n.
          simpl.
          unfold P4A.st_size.
          Lia.lia.
        }
        pose (buf'' := rewrite_size Hsz'' (n_tuple_take_n n (n_tuple_skip_n 0 buf'))).
        pose proof (wp_op'_spec_r c valu o 0 0 phi' (conf_store q2) buf' buf'' _ (conf_buf q1) (conf_store q1)) as wp_op'_spec.
        specialize (wp_op'_spec ltac:(eauto using rewrite_size_jmeq)).
        eapply interp_store_rel_congr in H0;
          [eapply wp_op'_spec in H0 | | | |];
          eauto;
          [|subst; now eauto using rewrite_size_jmeq].
        unfold phi' in H0.
        rewrite <- brimpl_corr in H0.
        autorewrite with interp_store_rel in H0.
        rewrite sr_subst_buf in H0; simpl; eauto.
        simpl in H0.
        autorewrite with interp_bit_expr in *.
        simpl (l2t nil) in *.
        assert (conf_buf_len q2 + length bs = size' (P4A.interp a) (conf_state q2)).
        {
          rewrite Hst.
          autorewrite with size'.
          unfold size; simpl.
          subst bs.
          rewrite t2l_len.
          Lia.lia.
        }
        assert (Hnil: conf_buf_len q2' = 0).
        {
          subst q2'.
          eapply conf_buf_len_follow_transition; eauto.
        }
        generalize (conf_buf q2').
        rewrite Hnil.
        intros.
        destruct n0.
        eapply interp_store_rel_congr; try eapply H0; eauto.
        * (* need lemma saying that conf_store is eval_op after a transition *)
          assert (Hfb: size' _ (conf_state q2) = conf_buf_len q2 + length bs).
          {
            rewrite Hst.
            autorewrite with size'.
            simpl.
            rewrite H3.
            rewrite t2l_len.
            rewrite Hlen.
            Lia.lia.
          }
          set (full_buf := rewrite_size Hfb (n_tuple_concat (conf_buf q2) (l2t bs))).
          assert (full_buf ~= n_tuple_concat (conf_buf q2) (l2t bs))
            by eapply rewrite_size_jmeq.
          assert (Hfb': size' _ (inl s) = size' _ (conf_state q2))
            by now rewrite Hst.
          set (full_buf' := rewrite_size Hfb' full_buf).
          assert (full_buf' ~= full_buf)
            by eapply rewrite_size_jmeq.
          subst q2'.
          erewrite conf_store_follow_transition; eauto.
          replace (update' (P4A.interp a) (conf_state q2) full_buf (conf_store q2))
            with (update' (P4A.interp a) (inl s) full_buf' (conf_store q2))
            by (apply update'_congr; eauto).
          autorewrite with update'.
          simpl.
          unfold P4A.update.
          apply eval_op_congr'; eauto.
          unfold buf''.
          destruct (plus_O_n _); simpl.
          etransitivity;
            [|symmetry; eapply rewrite_size_jmeq].
          eapply JMeq_trans with (y:=full_buf); eauto.
          unfold buf'.
          apply t2l_eq.
          rewrite t2l_n_tuple_take_n, t2l_n_tuple_skip_n.
          rewrite skipn_O.
          replace n with (length (t2l (rewrite_size Hsz' buf))).
          rewrite firstn_all.
          apply t2l_proper.
          etransitivity;
            [|symmetry; apply rewrite_size_jmeq].
          rewrite Heqbuf.
          etransitivity.
          apply H2.
          rewrite H3.
          apply n_tuple_concat_congr; eauto.
          etransitivity.
          eapply l2t_t2l.
          reflexivity.
          unfold n.
          rewrite t2l_len.
          unfold P4A.size, P4A.st_size.
          Lia.lia.
        * assert (Hnz: n = conf_buf_len q2 + length bs).
          {
            subst n.
            rewrite Hst in *.
            autorewrite with size' in *.
            simpl in *.
            unfold P4A.size in *.
            unfold P4A.st_size in *.
            Lia.lia.
          }
          unfold jump_cond.
          rewrite Hprevst.
          apply trans_cond_safe.
          destruct H1.
          rewrite H1.
          rewrite H5.
          erewrite conf_state_follow_transition; eauto.
          autorewrite with transitions'; simpl.
          unfold P4A.transitions.
          change ConfRel.P4A.eval_trans with P4A.eval_trans.
          assert (Hfb: size' _ (conf_state q2) = conf_buf_len q2 + length bs).
          {
            rewrite Hst.
            autorewrite with size'.
            rewrite <- Hnz.
            unfold n.
            reflexivity.
          }
          pose (full_buf := rewrite_size Hfb (n_tuple_concat (conf_buf q2) (l2t bs))).
          erewrite conf_store_follow_transition with (full_buf := full_buf); eauto using rewrite_size_jmeq.
          f_equal.
          autorewrite with update'.
          replace (update' (ConfRel.P4A.interp a) (conf_state q2) full_buf (conf_store q2))
            with (update (P4A.interp a) s buf'' (conf_store q2)).
          simpl.
          unfold P4A.update.
          eapply eval_op_congr'; eauto.
          destruct (plus_O_n _); reflexivity.
          rewrite <- update'_equation_1.
          apply update'_congr; eauto.
          unfold buf'', buf', full_buf.
          etransitivity.
          apply rewrite_size_jmeq.
          etransitivity;
            [|symmetry; apply rewrite_size_jmeq].
          apply t2l_eq.
          rewrite t2l_n_tuple_take_n.
          rewrite t2l_n_tuple_skip_n.
          rewrite skipn_O.
          replace n with (length (t2l (rewrite_size Hsz' buf))).
          rewrite firstn_all.
          apply eq_t2l.
          etransitivity.
          eapply rewrite_size_jmeq.
          rewrite Heqbuf.
          subst bs.
          apply n_tuple_concat_congr; eauto.
          symmetry; apply l2t_t2l.
          rewrite t2l_len.
          rewrite Hnz.
          subst bs.
          rewrite t2l_len.
          Lia.lia.
      + assert (Hbs: length bs > 0).
        {
          pose proof (conf_room_nonzero q2).
          subst bs.
          rewrite t2l_len.
          destruct H2 as [Hlen | [b' [Hst' Hlen]]];
            Lia.lia.
        }
        unfold kind_leap_size in *.
        rewrite sr_subst_buf in H0 by (simpl; eauto).
        simpl in *.
        autorewrite with interp_bit_expr in *.
        replace (conf_store q2') with (conf_store q2)
          by (symmetry;
              rewrite H5;
              eapply follow_done_store; eauto).
        set (buf' := conf_buf q2').
        pose proof (conf_buf_sane q2').
        rewrite H5 in H.
        erewrite follow_finish in H; eauto.
        autorewrite with size' in *.
        assert (conf_buf_len (follow q2 bs) = 0) by Lia.lia.
        assert (Hzero: conf_buf_len q2' = 0) by congruence.
        generalize buf'.
        clear buf'.
        rewrite Hzero.
        intros buf'.
        destruct buf'.
        auto.
        Unshelve.
        all: try exact 0.
        all: try exact tt.
  Qed.

  Lemma wp_lpred_pair_safe:
    forall (c: bctx) si (valu: bval c) b prev cur k phi q1 q2,
      interp_store_rel (wp_lpred (a:=a) si b prev cur k phi) valu (conf_buf q1) (conf_buf q2) (conf_store q1) (conf_store q2) ->
      interp_state_template prev (pick si (q1, q2)) ->
      forall bs (q1' q2': conf),
        interp_state_template cur (pick si (q1', q2')) ->
        kind_leap_size si k q1 q2 (check_bvar b) ->
        bs = t2l (interp_bvar valu b) ->
        q1' = pick si (follow q1 bs, q1) ->
        q2' = pick si (q2, follow q2 bs) ->
        interp_store_rel phi valu (conf_buf q1') (conf_buf q2') (conf_store q1') (conf_store q2').
  Proof.
    destruct k; eauto using wp_lpred_pair_jump_safe, wp_lpred_pair_read_safe.
  Qed.

  Lemma weaken_expr_size:
    forall c n (e: bit_expr Hdr c) l1 l2,
      be_size Hdr_sz l1 l2 (weaken_bit_expr n e) = be_size Hdr_sz l1 l2 e.
  Proof.
    induction e; intros; try destruct a0; simpl; auto.
    rewrite !IHe.
    reflexivity.
  Qed.

  Lemma weaken_bvar_interp:
    forall (c: bctx) (n: nat) (valu: bval c) (bits: n_tuple bool n) (b: bvar c),
    interp_bvar ((valu, bits): bval (BCSnoc c n)) (weaken_bvar n b) ~= interp_bvar valu b.
  Proof.
    destruct b, valu; simpl; autorewrite with interp_bvar; reflexivity.
  Qed.

  Lemma weaken_expr_interp:
    forall c n e (valu: bval c) (bits: n_tuple bool n) l1 l2 (buf1: n_tuple bool l1) (buf2: n_tuple bool l2) store1 store2,
      interp_bit_expr (weaken_bit_expr n e) (valu, bits) buf1 buf2 store1 store2 ~=
      interp_bit_expr (a:=a) e valu buf1 buf2 store1 store2.
  Proof.
    induction e; intros; simpl; autorewrite with interp_bit_expr in *.
    - auto.
    - destruct a0; autorewrite with interp_bit_expr; auto.
    - destruct a0; simpl; auto.
    - apply weaken_bvar_interp.
    - set (v1 := interp_bit_expr (weaken_bit_expr n e) (valu, bits) buf1 buf2 store1
                               store2).
      set (v2 := interp_bit_expr e valu buf1 buf2 store1 store2).
      assert (Hvv: v1 ~= v2) by eauto.
      revert Hvv.
      generalize v1 as x1, v2 as x2.
      generalize (be_size Hdr_sz l1 l2 (weaken_bit_expr n e)).
      generalize (be_size Hdr_sz l1 l2 e).
      intros.
      inversion Hvv.
      apply n_tuple_inj in H0.
      revert Hvv.
      clear H2 H.
      revert x1.
      rewrite H0.
      intros.
      rewrite Hvv.
      auto.
    - set (v11 := interp_bit_expr (weaken_bit_expr n e1) (valu, bits) buf1 buf2 store1
                               store2).
      set (v12 := interp_bit_expr e1 valu buf1 buf2 store1 store2).
      set (v21 := interp_bit_expr (weaken_bit_expr n e2) (valu, bits) buf1 buf2 store1
                               store2).
      set (v22 := interp_bit_expr e2 valu buf1 buf2 store1 store2).
      assert (Hv1: v11 ~= v12) by eauto.
      assert (Hv2: v21 ~= v22) by eauto.
      revert Hv1 Hv2.
      generalize v11 as x11, v12 as x12.
      generalize v21 as x21, v22 as x22.
      generalize (be_size Hdr_sz l1 l2 (weaken_bit_expr n e1)).
      generalize (be_size Hdr_sz l1 l2 e1).
      generalize (be_size Hdr_sz l1 l2 (weaken_bit_expr n e2)).
      generalize (be_size Hdr_sz l1 l2 e2).
      intros.
      inversion Hv1.
      inversion Hv2.
      clear H2 H H4 H5.
      apply n_tuple_inj in H0.
      apply n_tuple_inj in H3.
      subst n3.
      subst n1.
      rewrite Hv1, Hv2.
      reflexivity.
  Qed.

  Lemma weaken_rel_interp:
    forall c (valu: bval c) n rel (bits: n_tuple bool n) l1 l2 (buf1: n_tuple bool l1) (buf2: n_tuple bool l2) store1 store2,
      interp_store_rel rel valu buf1 buf2 store1 store2 <->
      interp_store_rel (a:=a) (weaken_store_rel n rel) (valu, bits) buf1 buf2 store1 store2.
  Proof.
    induction rel; intros; simpl; autorewrite with interp_store_rel in *.
    - split; auto.
    - split; auto.
    - destruct (Classes.eq_dec _ _); destruct (Classes.eq_dec _ _).
      + assert (He1: interp_bit_expr (weaken_bit_expr n e1) (valu, bits) buf1 buf2 store1 store2 ~=
                                interp_bit_expr (a:=a) e1 valu buf1 buf2 store1 store2)
          by auto using weaken_expr_interp.
        assert (He2: interp_bit_expr (weaken_bit_expr n e2) (valu, bits) buf1 buf2 store1 store2 ~=
                                interp_bit_expr (a:=a) e2 valu buf1 buf2 store1 store2)
          by auto using weaken_expr_interp.
        revert He1 He2.
        generalize (interp_bit_expr (weaken_bit_expr n e1) (valu, bits) buf1 buf2 store1 store2).
        generalize (interp_bit_expr (weaken_bit_expr n e2) (valu, bits) buf1 buf2 store1 store2).
        generalize (interp_bit_expr (a:=a) e1 valu buf1 buf2 store1 store2).
        generalize (interp_bit_expr (a:=a) e2 valu buf1 buf2 store1 store2).
        revert e.
        revert e0.
        rewrite !weaken_expr_size.
        generalize (be_size Hdr_sz l1 l2 e2).
        generalize (be_size Hdr_sz l1 l2 e1).
        intros.
        subst n0.
        rewrite He1, He2.
        rewrite <- !Eqdep_dec.eq_rect_eq_dec; auto using PeanoNat.Nat.eq_dec.
        tauto.
      + exfalso.
        rewrite !weaken_expr_size in *.
        congruence.
      + exfalso.
        rewrite !weaken_expr_size in *.
        congruence.
      + tauto.
    - rewrite <- brand_corr.
      autorewrite with interp_store_rel in *.
      rewrite IHrel1, IHrel2 by eauto.
      intuition eauto.
    - rewrite <- bror_corr.
      autorewrite with interp_store_rel in *.
      rewrite IHrel1, IHrel2 by eauto.
      intuition eauto.
    - rewrite IHrel1, IHrel2 by eauto.
      intuition eauto.
  Qed.

  Lemma leap_size_read_bound1:
    forall bs t1 t1' (q1 q2: conf),
      interp_state_template t1 q1 ->
      interp_state_template t1' (follow q1 bs) ->
      length bs = leap_size _ q1 q2 ->
      leap_kind t1 t1' = Read ->
      length bs < configuration_room_left q1.
  Proof.
    intros.
    pose proof (leap_size_nonzero q1 q2).
    unfold leap_size, leap_kind in *.
    destruct (st_buf_len t1') eqn:?; try congruence.
    destruct (conf_state q1) eqn:?, (conf_state q2) eqn:?.
    - assert (Hle: length bs <= configuration_room_left q1).
      {
        pose proof (Min.min_spec (configuration_room_left q1)
                                 (configuration_room_left q2)).
        intuition Lia.lia.
      }
      destruct (Compare_dec.le_lt_eq_dec _ _ Hle);
        [assumption|].
      assert (conf_buf_len (follow q1 bs) = 0).
      {
        apply Syntax.P4A.conf_buf_len_follow_transition.
        unfold configuration_room_left in *.
        pose proof (conf_buf_sane q1).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q1 bs) = 0).
      {
        apply Syntax.P4A.conf_buf_len_follow_transition.
        unfold configuration_room_left in *.
        pose proof (conf_buf_sane q1).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q1 bs) = 0).
      {
        eapply conf_buf_len_done.
        eapply follow_finish; eauto.
        pose proof (conf_room_nonzero q2).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q1 bs) = 0).
      {
        eapply conf_buf_len_done.
        eapply follow_finish; eauto.
        pose proof (conf_room_nonzero q2).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
  Qed.

  Lemma leap_size_read_bound2:
    forall bs t2 t2' (q1 q2: conf),
      interp_state_template t2 q2 ->
      interp_state_template t2' (follow q2 bs) ->
      length bs = leap_size _ q1 q2 ->
      leap_kind t2 t2' = Read ->
      length bs < configuration_room_left q2.
  Proof.
    intros.
    pose proof (leap_size_nonzero q1 q2).
    unfold leap_size, leap_kind in *.
    destruct (st_buf_len t2') eqn:?; try congruence.
    destruct (conf_state q1) eqn:?, (conf_state q2) eqn:?.
    - assert (Hle: length bs <= configuration_room_left q2).
      {
        pose proof (Min.min_spec (configuration_room_left q1)
                                 (configuration_room_left q2)).
        intuition Lia.lia.
      }
      destruct (Compare_dec.le_lt_eq_dec _ _ Hle);
        [assumption|].
      assert (conf_buf_len (follow q2 bs) = 0).
      {
        apply Syntax.P4A.conf_buf_len_follow_transition.
        unfold configuration_room_left in *.
        pose proof (conf_buf_sane q2).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q2 bs) = 0).
      {
        eapply conf_buf_len_done.
        eapply follow_finish; eauto.
        pose proof (conf_room_nonzero q1).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q2 bs) = 0).
      {
        apply Syntax.P4A.conf_buf_len_follow_transition.
        unfold configuration_room_left in *.
        pose proof (conf_buf_sane q1).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
    - assert (conf_buf_len (follow q2 bs) = 0).
      {
        eapply conf_buf_len_done.
        eapply follow_finish; eauto.
        pose proof (conf_room_nonzero q1).
        Lia.lia.
      }
      unfold interp_state_template in *.
      Lia.lia.
  Qed.

  Lemma leap_size_jump_bound1:
    forall bs t1 t1' (q1 q2: conf),
      interp_state_template t1 q1 ->
      interp_state_template t1' (follow q1 bs) ->
      length bs = leap_size _ q1 q2 ->
      leap_kind t1 t1' = Jump ->
      length bs = configuration_room_left q1 \/
      exists b, conf_state q1 = inr b.
  Proof.
    intros.
    unfold leap_kind in *.
    destruct (st_buf_len t1') eqn:?; [|discriminate].
    assert (conf_buf_len (follow q1 bs) = 0).
    {
      unfold interp_state_template in H0.
      intuition congruence.
    }
    destruct (conf_state q1) eqn:Hst.
    - left.
      unfold leap_size in *.
      rewrite Hst in *.
      destruct (conf_state q2); eauto.
      pose proof (Min.min_spec (configuration_room_left q1)
                               (configuration_room_left q2)).
      intuition.
      + congruence.
      + rewrite H6 in H1.
        pose proof (conf_room_nonzero q2).
        destruct (Compare_dec.le_lt_eq_dec _ _ H4);
          [|congruence].
        assert (Heq: conf_buf_len (follow q1 bs) =
                     conf_buf_len q1 + length bs).
        {
          apply conf_buf_len_follow_fill;
            unfold configuration_room_left in *;
            Lia.lia.
        }
        rewrite H3 in Heq.
        pose proof (conf_buf_sane q1).
        Lia.lia.
    - right.
      eauto.
  Qed.

  Lemma leap_size_jump_bound2:
    forall bs t2 t2' (q1 q2: conf),
      interp_state_template t2 q2 ->
      interp_state_template t2' (follow q2 bs) ->
      length bs = leap_size _ q1 q2 ->
      leap_kind t2 t2' = Jump ->
      length bs = configuration_room_left q2 \/
      exists b, conf_state q2 = inr b.
  Proof.
    intros.
    unfold leap_kind in *.
    destruct (st_buf_len t2') eqn:?; [|discriminate].
    assert (conf_buf_len (follow q2 bs) = 0).
    {
      unfold interp_state_template in H0.
      intuition congruence.
    }
    destruct (conf_state q2) eqn:Hst.
    - left.
      unfold leap_size in *.
      rewrite Hst in *.
      destruct (conf_state q1); eauto.
      pose proof (Min.min_spec (configuration_room_left q1)
                               (configuration_room_left q2)).
      intuition.
      + rewrite H6 in H1.
        pose proof (conf_room_nonzero q1).
        assert (Heq: conf_buf_len (follow q2 bs) =
                     conf_buf_len q2 + length bs).
        {
          apply conf_buf_len_follow_fill;
            unfold configuration_room_left in *;
            Lia.lia.
        }
        rewrite H3 in Heq.
        pose proof (conf_buf_sane q2).
        Lia.lia.
      + congruence.
    - right.
      eauto.
  Qed.

  Lemma wp_pred_pair_safe:
    forall size phi t1 t2 q1 q2,
      interp_state_template t1 q1 ->
      interp_state_template t2 q2 ->
      interp_conf_rel a (wp_pred_pair (a:=a) phi (size, (t1, t2))) q1 q2 ->
      forall bs,
        length bs = size ->
        size = leap_size _ q1 q2 ->
        interp_conf_rel a phi (follow q1 bs) (follow q2 bs).
  Proof.
    unfold wp_pred_pair.
    intros.
    unfold interp_conf_rel, interp_conf_state in *.
    simpl in *.
    intuition.
    pose proof H.
    pose proof H0.
    pose proof H5.
    pose proof H7.
    unfold interp_state_template in H, H0, H5, H7.
    simpl in *.
    intuition.
    pose (eq_rect (length bs) (fun x => n_tuple bool x) (l2t bs) size H2) as bits.
    cut (interp_store_rel (weaken_store_rel size (cr_rel phi)) (valu, bits) (conf_buf (follow q1 bs))
           (conf_buf (follow q2 bs)) (conf_store (follow q1 bs))
           (conf_store (follow q2 bs))).
    {
      eapply weaken_rel_interp; auto.
    }
    destruct phi as [[? ?] ? ?].
    simpl in *.
    assert (follow q1 bs =
            follow q1 (t2l (interp_bvar ((valu, bits):bval (BCSnoc _ _)) (BVarTop cr_ctx size)))).
    {
      subst bits.
      subst size.
      simpl.
      autorewrite with interp_bvar.
      rewrite t2l_l2t.
      reflexivity.
    }
    assert (follow q2 bs =
            follow q2 (t2l (interp_bvar ((valu, bits):bval (BCSnoc _ _)) (BVarTop cr_ctx size)))).
    {
      subst bits.
      subst size.
      simpl.
      autorewrite with interp_bvar.
      rewrite t2l_l2t.
      reflexivity.
    }
    simpl in *.
    assert (size >= 1).
    {
      pose proof (leap_size_nonzero q1 q2).
      Lia.lia.
    }
    eapply wp_lpred_pair_safe with (si:=Right); simpl.
    eapply wp_lpred_pair_safe with (si:=Left); simpl.
    all:eauto.
    + unfold kind_leap_size.
      destruct (leap_kind t1 cs_st1) eqn:Hlk.
      * pose proof (leap_size_jump_bound1 bs t1 cs_st1 q1 q2
                   ltac:(unfold interp_state_template; eauto)
                   ltac:(unfold interp_state_template; eauto)
                   ltac:(congruence) ltac:(congruence))
             as Hbound.
        simpl in *.
        subst size.
        destruct Hbound as [Hbound | [b Hbound]];
          eauto.
      * simpl.
        subst size.
        eapply leap_size_read_bound1;
          unfold interp_state_template;
          intuition.
    + unfold kind_leap_size.
      destruct (leap_kind t2 cs_st2) eqn:Hlk.
      * pose proof (leap_size_jump_bound2 bs t2 cs_st2 q1 q2
                   ltac:(unfold interp_state_template; eauto)
                   ltac:(unfold interp_state_template; eauto)
                   ltac:(congruence) ltac:(congruence))
             as Hbound.
        simpl in *.
        subst size.
        destruct Hbound as [Hbound | [b Hbound]];
          eauto.
      * simpl.
        subst size.
        eapply leap_size_read_bound2;
          unfold interp_state_template;
          intuition.
  Qed.

  (* Soundness of weakest precondition operator. *)
  Theorem wp_safe:
    forall top r phi q1 q2,
      In (conf_to_state_template q1, conf_to_state_template q2) r ->
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
    unfold wp in H.
    simpl in *.
    set (r' := map (wp_pred_pair phi)
                   (flat_map (Reachability.reaches (phi_st1, phi_st2))
                             r))
      in *.
    unfold interp_crel in H.
    assert (forall size st,
               In st r ->
               In (size, st)
                  (Reachability.reaches (cs_st1 (cr_st phi), cs_st2 (cr_st phi)) st) ->
               interp_conf_rel a (wp_pred_pair phi (size, st)) q1 q2).
    {
      subst phi.
      pose proof (Relations.interp_rels_in _ _ _ _ _ H0).
      setoid_rewrite in_map_iff in H3.
      intros.
      subst r'.
      repeat (setoid_rewrite in_map_iff in H3 || setoid_rewrite in_flat_map in H3).
      simpl in *.
      eapply H3.
      destruct st in *; simpl in *.
      intuition.
      eexists; intuition eauto.
      eexists; intuition eauto.
      intuition.
    }
    set (st1 := {| st_state := conf_state q1;
                   st_buf_len := conf_buf_len q1|}).
    set (st2 := {| st_state := conf_state q2;
                   st_buf_len := conf_buf_len q2|}).
    set (qst := {|cs_st1 := st1; cs_st2 := st2|}).
    change phi_st1 with (fst (phi_st1, phi_st2)) in H1.
    change phi_st2 with (snd (phi_st1, phi_st2)) in H1.
    destruct (Reachability.reachable_pair_step' (st1, st2)) eqn:?.
    assert (In (length bs, (st1, st2)) (Reachability.reaches (a:=a) (phi_st1, phi_st2) (st1, st2))).
    {
      eapply Reachability.follow_in_reaches with (c1 := q1) (c2 := q2);
        try solve [cbv; tauto
                  |unfold interp_conf_state in H2;
                   subst q1' q2';
                   simpl in H2;
                   tauto].
      now rewrite reads_left_config_left with (q1 := q1) (q2 := q2).
    }
    assert (Hpairq: interp_conf_rel a (wp_pred_pair phi (length bs, (st1, st2))) q1 q2).
    {
      eapply H3; eauto.
      subst phi.
      eapply H4.
    }
    assert (interp_state_template st1 q1)
     by (unfold interp_state_template; simpl; tauto).
    assert (interp_state_template st2 q2)
     by (unfold interp_state_template; simpl; tauto).
    eapply (wp_pred_pair_safe (length bs) phi st1 st2 q1 q2) in Hpairq; eauto.
    unfold interp_conf_rel in Hpairq.
    subst phi q1' q2'.
    eauto.
  Qed.

End WPProofs.

(* Print Assumptions wp_safe. *)
