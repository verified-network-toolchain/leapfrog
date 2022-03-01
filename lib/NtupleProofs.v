Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import Leapfrog.FinType.
Require Import Leapfrog.TypeNeq.
Require Import Leapfrog.Ntuple.

Set Universe Polymorphism.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import Coq.PArith.BinPos.

(*
Definition enum_tuples (n: N) : list (n_tuple bool n) :=
  N.peano_rect (fun n => list (n_tuple bool n)) (n_tuple_emp :: nil) (fun _ shorter =>
    map (fun t => n_tuple_cons_succ t false) shorter ++
    map (fun t => n_tuple_cons_succ t true) shorter
  ) n.

Lemma length_enum_tuples:
  forall n,
    length (enum_tuples n) = N.to_nat (2 ^ n).
Proof.
  intros.
  induction n using N.peano_rec.
  - reflexivity.
  - simpl.
    unfold enum_tuples.
    erewrite N.peano_rect_succ.
    fold (enum_tuples n).
    rewrite app_length.
    repeat rewrite map_length.
    repeat rewrite IHn.
    erewrite N.pow_succ_r; [|Lia.lia].
    erewrite N2Nat.inj_mul.
    simpl.
    Lia.lia.
Qed.

Definition code (n: N) : n_tuple bool n -> nat.
refine (
  N.peano_rect (fun n => n_tuple bool n -> nat) (fun _ => 0) _ n
).
clear n.
refine (
  fun n r t => _
).
destruct t.
destruct x; [exfalso; shelve|].
destruct b eqn:?.
- N.of_nat (2 ^ n) +


inversion l.
  match n as n' return n_tuple bool n' -> nat with
  | 0 => fun _ => 0
  | S n =>
    fun t =>
    let '(t, b) := t in
    match b with
    | false => code n t
    | true => Nat.pow 2 n + code n t
    end
  end.

Lemma code_bound:
  forall n (t: n_tuple bool n),
    code n t < Nat.pow 2 n.
Proof.
  induction n; intros; destruct t; simpl.
  - Lia.lia.
  - destruct b; specialize (IHn n0); Lia.lia.
Qed.

Lemma code_nth:
  forall n (x: n_tuple bool n),
    nth_error (enum_tuples n) (code n x) = Some x.
Proof.
  induction n; intros.
  - now destruct x.
  - simpl enum_tuples.
    destruct x.
    specialize (IHn n0).
    destruct b; simpl code.
    + rewrite nth_error_app2;
      rewrite <- length_enum_tuples, map_length; [|Lia.lia].
      apply map_nth_error with (f := fun t => (t, true)).
      generalize (length (enum_tuples n)).
      intro n1.
      replace (n1 + code n n0 - n1) with (code n n0) by Lia.lia.
      exact IHn.
    + rewrite nth_error_app1.
      * now apply map_nth_error with (f := fun t => (t, false)).
      * rewrite map_length.
        rewrite length_enum_tuples.
        apply code_bound.
Qed.
*)

Global Instance BoolTupleFinite (n: N): Finite (n_tuple bool n).
Admitted.
(*
  {| enum := enum_tuples n |}.
Next Obligation.
  induction n using N.peano_ind.
  - simpl.
    constructor.
    + intro; contradiction.
    + constructor.
  - unfold enum_tuples.
    erewrite N.peano_rect_succ.
    fold (enum_tuples n).
    apply NoDup_app.
    + apply NoDup_map; auto.
      intros.
      inversion H.
      clear H.
      destruct x; destruct y.
      simpl in *;
      subst.
      pose proof lenpf_uniq _ _ _ l l0.
      subst.
      exact eq_refl.
    + apply NoDup_map; auto.
      intros.
      inversion H.
      clear H.
      destruct x; destruct y.
      simpl in *;
      subst.
      pose proof lenpf_uniq _ _ _ l l0.
      subst.
      exact eq_refl.
    + intros; intro.
      rewrite in_map_iff in *.
      destruct H as [x0 [? _]], H0 as [x1 [? _]].
      unfold n_tuple_cons_succ in *.
      simpl in *.
      congruence.
    + intros; intro.
      rewrite in_map_iff in *.
      destruct H as [x0 [? _]], H0 as [x1 [? _]].
      unfold n_tuple_cons_succ in *.
      simpl in *.
      congruence.
Qed.
Next Obligation.
  induction n using N.peano_ind.
  - left.
    erewrite n_tuple_emp_uniq.
    exact eq_refl.
  -
  eapply nth_error_In.
  eapply code_nth.
Qed.

Lemma unit_type_neq:
  forall T,
    (unit:Type) = T ->
    forall (x y: T),
      x <> y ->
      False.
Proof.
  intros T Ht.
  rewrite <- Ht.
  intros [] [].
  congruence.
Qed.

Lemma n_tuple_diff_neq:
  forall n m,
    n <> m ->
    not (@eq Type (n_tuple bool n) (n_tuple bool m)).
Proof.
  intros.
  eapply TypeNeq.card_neq.
  cbn.
  rewrite !length_enum_tuples.
  intro Hpow.
  eapply PeanoNat.Nat.pow_inj_r in Hpow; auto.
Qed.

Lemma n_tuple_succ_inj:
  forall n m,
    n_tuple bool (1 + n) = n_tuple bool (1 + m) ->
    n_tuple bool n = n_tuple bool m.
Proof.
  intros n m.
  destruct (PeanoNat.Nat.eq_dec n m).
  - subst m.
    eauto.
  - intros.
    exfalso.
    eapply n_tuple_diff_neq; [|eassumption].
    eauto.
Qed.

Lemma n_tuple_inj:
  forall n m,
    @eq Type (n_tuple bool n) (n_tuple bool m) ->
    n = m.
Proof.
  intros.
  destruct (PeanoNat.Nat.eq_dec n m); auto.
  exfalso.
  eapply n_tuple_diff_neq; eauto.
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
*)
Lemma t2l_eq:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    t2l xs = t2l ys ->
    xs ~= ys.
Proof.
Admitted.
  (* intros.
  pose proof (t2l_n_eq _ _ _ _ H).
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
      apply f_equal with (f := (fun l => (@last bool) l false)) in H.
      erewrite !last_last in H.
      congruence.
    }
    subst b0.
    apply app_inv_tail in H.
    apply IHn in H.
    congruence.
Qed. *)
(*

Lemma eq_t2l:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    xs ~= ys ->
    t2l xs = t2l ys.
Proof.
  intros.
  inversion H.
  assert (n = m).
  eapply n_tuple_inj.
  apply H1.
  subst m.
  rewrite H.
  reflexivity.
Qed.

Lemma inv_jmeq_size:
  forall n (xs: n_tuple bool n) m (ys: n_tuple bool m),
    xs ~= ys ->
    n = m.
Proof.
  intros.
  eapply n_tuple_inj.
  now inversion H.
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
      apply inv_jmeq_size in H.
      Lia.lia.
  - destruct m, xs; destruct ys.
    + exfalso.
      apply inv_jmeq_size in H.
      Lia.lia.
    + pose proof (inv_jmeq_size _ _ _ _ H).
      assert (n = m) by Lia.lia.
      subst m.
      simpl_JMeq.
      simpl in *.
      inversion H.
      subst b0.
      pose proof (IHn _ n0 x n1 y ltac:(rewrite H2; reflexivity)).
      destruct H1.
      split; [|auto].
      rewrite H1.
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
*)
Lemma concat_proper:
  forall n1 m1 (xs1: n_tuple bool n1) (ys1: n_tuple bool m1)
    n2 m2 (xs2: n_tuple bool n2) (ys2: n_tuple bool m2),
    xs1 ~= xs2 ->
    ys1 ~= ys2 ->
    n_tuple_concat xs1 ys1 ~= n_tuple_concat xs2 ys2.
Admitted.
(*
Proof.
  intros.
  assert (n1 = n2) by (eapply inv_jmeq_size; eauto).
  assert (m1 = m2) by (eapply inv_jmeq_size; eauto).
  revert H H0.
  revert xs2 ys2.
  revert xs1 ys1.
  subst n2.
  subst m2.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma t2l_proper:
  forall n m (xs: n_tuple bool n) (ys: n_tuple bool m),
    xs ~= ys ->
    t2l xs = t2l ys.
Proof.
  intros.
  inversion H.
  apply n_tuple_inj in H1.
  subst n.
  apply JMeq_eq in H.
  congruence.
Qed.

Lemma pair_proper:
  forall A B C D (a: A) (b: B) (c: C) (d: D),
    a ~= b ->
    c ~= d ->
    (a, c) ~= (b, d).
Proof.
  intros.
  inversion H.
  inversion H0.
  subst.
  reflexivity.
Qed.

Lemma concat'_snoc:
  forall n m (xs: n_tuple bool n) x (ys: n_tuple bool m),
    n_tuple_concat' ((xs, x): n_tuple bool (S n)) ys ~= n_tuple_concat' xs (n_tuple_cons ys x).
Proof.
  induction m; intros.
  - auto.
  - destruct ys.
    change (n_tuple_concat' ((xs, x): n_tuple bool (S n)) ((n0, b): n_tuple bool (S m)))
      with (n_tuple_concat' ((xs, x): n_tuple bool (S n)) n0, b).
    simpl ((xs, x) : _).
    specialize (IHm xs x n0).
    eapply JMeq_trans with (y:=(n_tuple_concat' xs (n_tuple_cons n0 x), b)).
    apply pair_proper.
    eapply IHm.
    auto.
    reflexivity.
Qed.

Lemma t2l_concat':
  forall n m (xs: n_tuple bool n) (ys: n_tuple bool m),
    t2l (n_tuple_concat' xs ys) = t2l xs ++ t2l ys.
Proof.
  induction n; intros.
  - simpl in *.
    assert (@n_tuple_concat' _ O m tt ys ~= ys)
      by (apply (concat'_emp _ m ys); auto).
    apply t2l_proper in H.
    destruct xs.
    congruence.
  - destruct xs as [xs x].
    simpl in *.
    assert (n_tuple_concat' ((xs, x): n_tuple bool (S n)) ys
            ~= n_tuple_concat' xs (n_tuple_cons ys x))
      by eapply concat'_snoc.
    apply t2l_proper in H.
    rewrite H.
    rewrite app_assoc_reverse.
    simpl (_ ++ _).
    rewrite IHn.
    rewrite t2l_cons.
    reflexivity.
Qed.

Lemma concat_concat':
  forall n m (xs: n_tuple bool n) (ys: n_tuple bool m),
    n_tuple_concat xs ys ~= n_tuple_concat' xs ys.
Proof.
  unfold n_tuple_concat.
  induction m; intros; simpl in *.
  - destruct ys.
    simpl in *.
    revert xs.
    rewrite <- (plus_zero_trans n).
    intros.
    apply rewrite_size_jmeq.
  - destruct ys as [ys y]; simpl in *.
    remember (n_tuple_concat' xs ys) as zs.
    remember (zs, y) as zsy.
    change ((n_tuple bool (m + n)%nat * bool)%type) with (n_tuple bool (S m + n)) in zsy.
    apply rewrite_size_jmeq.
Qed.
*)
Lemma t2l_concat:
  forall n m (xs: n_tuple bool n) (ys: n_tuple bool m),
    t2l (n_tuple_concat xs ys) = t2l xs ++ t2l ys.
Proof.
Admitted.
  (* intros.
  replace (t2l (n_tuple_concat xs ys)) with (t2l (n_tuple_concat' xs ys))
    by (eapply t2l_proper; symmetry; eapply concat_concat').
  apply t2l_concat'. *)
(* Qed. *)


Lemma n_tuple_concat_roundtrip:
  forall n m (t: n_tuple bool m),
    (n_tuple_concat (n_tuple_take_n n t) (n_tuple_skip_n n t)) ~= t.
Admitted.
(*
Proof.
  intros.
  unfold n_tuple_concat.
  rewrite rewrite_size_jmeq.
  apply NtupleProofs.t2l_eq.
  rewrite NtupleProofs.t2l_concat'.
  rewrite t2l_n_tuple_take_n, t2l_n_tuple_skip_n.
  apply List.firstn_skipn.
Qed.
*)

Lemma n_tuple_take_n_roundtrip:
  forall n (t: n_tuple bool n) k (t': n_tuple bool k),
    t ~= n_tuple_take_n n (n_tuple_concat t t')
.
Admitted.
(*
Proof.
  intros.
  apply t2l_eq.
  rewrite t2l_n_tuple_take_n.
  rewrite t2l_concat.
  rewrite firstn_app.
  rewrite t2l_len.
  replace (n - n) with 0 by Lia.lia.
  rewrite firstn_O.
  rewrite app_nil_r.
  rewrite <- firstn_all at 1.
  f_equal.
  apply t2l_len.
Qed.
*)
Lemma n_tuple_skip_n_roundtrip:
  forall n (t: n_tuple bool n) k (t': n_tuple bool k),
    t' ~= n_tuple_skip_n n (n_tuple_concat t t')
.
Admitted.
(*
Proof.
  intros.
  apply t2l_eq.
  rewrite t2l_n_tuple_skip_n.
  rewrite t2l_concat.
  rewrite skipn_app.
  rewrite <- app_nil_l at 1.
  rewrite <- skipn_all with (l := t2l t).
  repeat f_equal.
  apply t2l_len.
  rewrite t2l_len.
  replace (n - n) with 0 by Lia.lia.
  now rewrite skipn_O.
Qed.

Lemma eq_rect_jmeq (n n': nat) (buf: Ntuple.n_tuple bool n) H:
  eq_rect n _ buf n' H ~= buf.
Proof.
  subst.
  reflexivity.
Qed. *)

Lemma n_tuple_take_emp :
  forall {A} n, @n_tuple_take_n A _ n n_tuple_emp = n_tuple_emp.
Proof.
  intros.
  unfold n_tuple_take_n.
  induction (N.to_nat n); intuition eauto.
Qed.

Lemma n_tuple_skip_emp :
  forall {A} n, @n_tuple_skip_n A _ n n_tuple_emp = n_tuple_emp.
Proof.
  intros.
  unfold n_tuple_skip_n.
  induction (N.to_nat n); intuition eauto.
Qed.

Lemma n_tup_take_wf':
  forall A n m k (v: n_tuple A n),
    n_tup_wf v -> k = N.min m n -> n_tup_wf (n := k) (n_tuple_take_n m v).
Proof.
  unfold n_tup_wf; intros.
  apply len_pf_rev.
  apply len_pf_conv in H.
  unfold n_tuple_take_n.
  rewrite firstn_length.
  rewrite t2l_len.
  - Lia.lia.
  - now apply len_pf_rev.
Qed.

Lemma n_tup_take_wf :
  forall A n m (v: n_tuple A n),
    n_tup_wf v -> n_tup_wf (n_tuple_take_n m v).
Proof.
  intros.
  now apply n_tup_take_wf'.
Qed.

Lemma n_tup_skip_wf':
  forall A n m k (v: n_tuple A n),
    n_tup_wf v -> (k = n - m)%N -> n_tup_wf (n := k) (n_tuple_skip_n m v).
Proof.
  unfold n_tup_wf; intros.
  apply len_pf_rev.
  apply len_pf_conv in H.
  unfold n_tuple_skip_n.
  rewrite skipn_length.
  rewrite t2l_len.
  - Lia.lia.
  - now apply len_pf_rev.
Qed.

Lemma n_tup_skip_wf :
  forall A n m (v: n_tuple A n),
    n_tup_wf v -> n_tup_wf (n_tuple_skip_n m v).
Proof.
  intros.
  now eapply n_tup_skip_wf'.
Qed.

Lemma n_tup_cat_wf':
  forall A n m k (v : n_tuple A n) (v': n_tuple A m),
  n_tup_wf v ->
  n_tup_wf v' ->
  k = (n + m)%N ->
  n_tup_wf (n := k) (n_tuple_concat v v').
Proof.
  intros.
  apply len_pf_rev.
  apply len_pf_conv in H, H0.
  unfold n_tuple_concat.
  rewrite app_length.
  Lia.lia.
Qed.

Lemma n_tup_cat_wf :
  forall A n m (v : n_tuple A n) (v': n_tuple A m),
  n_tup_wf v ->
  n_tup_wf v' ->
  n_tup_wf (n_tuple_concat v v').
Proof.
  intros.
  now apply n_tup_cat_wf'.
Qed.
