Require Import Leapfrog.FinType.
Require Import Leapfrog.TypeNeq.

Require Import Coq.Classes.EquivDec.
Require Import Coq.Init.Peano.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Import ListNotations.

Set Universe Polymorphism.

Fixpoint n_tuple A (n: nat): Type :=
  match n with
  | 0 => unit
  | S n => n_tuple A n * A
  end.

Definition n_tuple_snoc {A n} (xs: n_tuple A n) (x: A) : n_tuple A (1 + n) :=
  (xs, x).

Fixpoint n_tuple_cons {A n} (xs: n_tuple A n) (x: A) : n_tuple A (1 + n) :=
  match n as n' return (n_tuple A n' -> n_tuple A (1 + n')) with
  | 0 =>
    fun _ => (tt, x)
  | S n =>
    fun '(xs, x') => (n_tuple_cons xs x, x')
  end xs.

Fixpoint t2l {A: Type} {n: nat} (x: n_tuple A n) : list A :=
  match n as n' return n_tuple A n' -> list A with
  | 0 => fun _ => nil
  | S n => fun p => t2l (fst p) ++ [snd p]
  end x.

Lemma t2l_len {A} n: forall (x: n_tuple A n), length (t2l x) = n.
Proof.
  induction n.
  - simpl; intros; trivial.
  - simpl; intros.
    erewrite app_length.
    simpl.
    erewrite <- plus_n_Sm.
    erewrite <- plus_n_O.
    erewrite IHn.
    trivial.
Qed.

Definition rewrite_size {A n m} (pf: m = n) (l: n_tuple A n) : n_tuple A m :=
  eq_rect_r (fun m' => n_tuple A m') l pf.

Fixpoint l2t {A: Type} (l: list A) : n_tuple A (length l) :=
  match l as l' return n_tuple A (length l') with
  | nil => tt
  | a::l => n_tuple_cons (l2t l) a
  end.

Fixpoint nat2t (n: nat) (v: nat) : n_tuple bool n :=
  match n as n' return n_tuple bool n' with
  | 0 => tt
  | S n =>
    (nat2t n (Nat.div2 v), Nat.eqb (Nat.modulo v 2) 1)
  end.

Fixpoint n_tuple_concat' {A n m} (xs: n_tuple A n) (ys: n_tuple A m) : n_tuple A (m + n) :=
  match m as m' return (n_tuple A m' -> n_tuple A (m' + n)) with
  | 0 =>
    fun _ => xs
  | S m0 =>
    fun '(ys, y) => (n_tuple_concat' xs ys, y)
  end ys.

Fixpoint n_tuple_repeat {A: Type} (n: nat) (a: A) : n_tuple A n :=
  match n with
  | 0 => tt
  | S n => ((n_tuple_repeat n a), a)
  end.

Definition p_l_trans x y : S x + y = S (x + y) := eq_refl.

Import EqNotations.

Definition plus_zero_trans : forall n, n + 0 = n.
  refine (fix pztrec n :=
    match n with
    | 0 => eq_refl
    | S n' =>
      let HR := pztrec n' in
      let HR' := p_l_trans n' 0 in
        _
    end
  ).
  rewrite HR'.
  rewrite HR.
  exact eq_refl.
  Defined.

Definition succ_add_trans (m: nat) : forall n, n + S m = S n + m.
  refine (fix satrec n {struct n} :=
    match n with
    | 0 => eq_refl
    | S m' =>
      let hr := satrec m' in
        _
    end
  ).
  simpl.
  rewrite hr.
  simpl.
  exact eq_refl.
  Defined.

Program Definition n_tuple_concat {A n m} (xs: n_tuple A n) (ys: n_tuple A m) : n_tuple A (n + m) :=
  rewrite_size _ (n_tuple_concat' xs ys).
Next Obligation.
  Lia.lia.
Defined.

Instance n_tuple_eq_dec
         {A: Type}
         `{A_eq_dec: EquivDec.EqDec A eq}
         (n: nat) : EquivDec.EqDec (n_tuple A n) eq.
Proof.
  unfold EquivDec.EqDec; intros.
  induction n.
  - destruct x, y; now left.
  - destruct x, y.
    destruct (A_eq_dec a a0).
    + destruct (IHn n0 n1).
      * left; congruence.
      * right; congruence.
    + right; congruence.
Defined.

Lemma min_0_r : forall n, Nat.min n 0 = 0.
Proof.
  intros.
  eapply min_r; eapply le_0_n.
Qed.
Lemma min_0_l : forall n, Nat.min 0 n = 0.
Proof.
  intros.
  eapply min_l; eapply le_0_n.
Qed.

Program Definition n_tuple_take_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (Nat.min n m) :=
  rewrite_size _ (l2t (firstn n (t2l xs))).
Next Obligation.
  rewrite firstn_length.
  rewrite t2l_len.
  exact eq_refl.
Defined.

Program Definition n_tuple_skip_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (m - n) :=
  rewrite_size _ (l2t (skipn n (t2l xs))).
Next Obligation.
  rewrite skipn_length.
  rewrite t2l_len.
  exact eq_refl.
Defined.

Program Definition n_tuple_slice {A n} (hi lo: nat) (xs: n_tuple A n) : n_tuple A (Nat.min (1 + hi) n - lo) :=
  n_tuple_skip_n lo (n_tuple_take_n (1 + hi) xs).

Lemma rewrite_size_eq:
  forall n (x: n_tuple bool n) (pf: n = n),
    Ntuple.rewrite_size pf x = x.
Proof.
  unfold Ntuple.rewrite_size, eq_rect_r.
  intros.
  rewrite <- eq_rect_eq_dec; eauto.
  apply PeanoNat.Nat.eq_dec.
Qed.

Lemma rewrite_size_jmeq:
  forall A n m (x: Ntuple.n_tuple A m) (pf: n = m),
    JMeq (Ntuple.rewrite_size pf x) x.
Proof.
  unfold Ntuple.rewrite_size, eq_rect_r.
  intros.
  destruct pf.
  reflexivity.
Qed.

Lemma concat'_emp:
  forall A n (t: n_tuple A n),
    JMeq (n_tuple_concat' (tt: n_tuple A 0) t) t.
Proof.
  induction n; simpl; destruct t.
  - eapply JMeq_refl.
  - erewrite IHn.
    eapply JMeq_refl.
Admitted. (* Right now, the kernel crashes on QED *)

Lemma concat_emp:
  forall A n (t: n_tuple A n),
    JMeq (n_tuple_concat (tt: n_tuple A 0) t) t.
Proof.
  unfold n_tuple_concat.
  unfold eq_rect_r.
  intros.
  pose proof (concat'_emp _ _ t).
  rewrite <- H.
  apply rewrite_size_jmeq.
Admitted.

Lemma concat'_cons:
  forall (A: Type) n m (xs: n_tuple A n) (ys: n_tuple A m) a,
    JMeq (n_tuple_cons (n_tuple_concat' xs ys) a)
         (n_tuple_concat' (n_tuple_cons xs a) ys).
Proof.
  intros.
  induction m; simpl; destruct ys.
  - reflexivity.
  - assert (JMeq (n_tuple_cons (n_tuple_concat' xs n0) a, a0)
                 (n_tuple_concat' (n_tuple_cons xs a) n0, a0))
      by (rewrite IHm; reflexivity).
    eauto using JMeq_trans.
Admitted.

Lemma concat_cons:
  forall (A: Type) n m (xs: n_tuple A n) (ys: n_tuple A m) a,
    JMeq (n_tuple_cons (n_tuple_concat xs ys) a)
         (n_tuple_concat (n_tuple_cons xs a) ys).
Proof.
  intros.
  unfold n_tuple_concat.
  generalize (n_tuple_concat_obligation_1 A (1 + n) m).
  generalize (n_tuple_concat_obligation_1 A n m).
  intros e e0.
  rewrite e, e0.
  replace (rewrite_size eq_refl _) with (n_tuple_concat' xs ys).
  replace (rewrite_size eq_refl _) with (n_tuple_concat' (n_tuple_cons xs a) ys).
  - now erewrite concat'_cons.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
Admitted.

Section ConvProofs.
  Set Universe Polymorphism.
  Variable (A: Type).

  Lemma l2t_app:
    forall (xs ys: list A),
      JMeq (l2t (xs ++ ys)) (n_tuple_concat (l2t xs) (l2t ys)).
  Proof.
    induction xs; cbn; intros.
    - apply JMeq_sym.
      apply concat_emp.
    - pose proof (IHxs ys).
      assert (JMeq (n_tuple_cons (l2t (xs ++ ys)) a)
                   (n_tuple_cons (n_tuple_concat (l2t xs) (l2t ys)) a)).
      {
        generalize dependent (l2t (xs ++ ys)).
        rewrite app_length.
        intros.
        rewrite H.
        reflexivity.
      }
      eapply JMeq_trans; [now apply H0|].
      pose proof @concat_cons A _ _ (l2t xs) (l2t ys) a.
      eapply H1.
  Qed.

  Lemma l2t_t2l:
    forall n (t: n_tuple A n),
      JMeq (l2t (t2l t)) t.
  Proof.
    induction n; intros; destruct t.
    - reflexivity.
    - cbn.
      pose proof (l2t_app (t2l n0) [a]).
      eapply JMeq_trans.
      eapply H.
      cbn.
      assert (JMeq
                (n_tuple_concat (l2t (t2l n0)) ((tt, a): n_tuple _ 1))
                (l2t (t2l n0), a)).
      {
        generalize (l2t (t2l n0)).
        generalize (length (t2l n0)).
        unfold n_tuple_concat.
        intro n1.
        generalize (n_tuple_concat_obligation_1 A n1 1).
        intros.
        cbn in *.
        apply rewrite_size_jmeq.
      }
      eapply JMeq_trans.
      eapply H0.
      eapply JMeq_sym.
      specialize (IHn n0).
      revert IHn.
      generalize dependent (l2t (t2l n0)).
      rewrite t2l_len.
      intros.
      rewrite IHn.
      reflexivity.
  Qed.

  Lemma t2l_cons:
    forall n (t: n_tuple A n) x,
      t2l (n_tuple_cons t x) = x :: t2l t.
  Proof.
    induction n.
    - reflexivity.
    - intros.
      destruct t.
      simpl.
      replace (x :: t2l n0 ++ [a])
        with ((x :: t2l n0) ++ [a])
        by eauto with datatypes.
      rewrite <- IHn.
      remember (n_tuple_cons n0 x) as g.
      simpl in *.
      now destruct g.
  Qed.

  Lemma t2l_l2t:
    forall (l: list A),
      Ntuple.t2l (l2t l) = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl (l2t _ ).
      replace (a :: l) with (a :: t2l (l2t l)) by (rewrite IHl; auto).
      apply t2l_cons.
  Qed.

End ConvProofs.

Lemma t2l_n_tuple_take_n:
  forall n m (t: n_tuple bool n),
    t2l (n_tuple_take_n m t) = firstn m (t2l t).
Proof.
  intros.
  unfold n_tuple_take_n.
  generalize (Ntuple.n_tuple_take_n_obligation_1 bool n m t).
  generalize (Nat.min m n).
  intros.
  subst.
  rewrite rewrite_size_eq.
  rewrite (t2l_l2t bool).
  reflexivity.
Qed.

Lemma t2l_n_tuple_skip_n:
  forall n m (t: n_tuple bool n),
    t2l (n_tuple_skip_n m t) = skipn m (t2l t).
Proof.
  intros.
  unfold n_tuple_skip_n.
  generalize (Ntuple.n_tuple_skip_n_obligation_1 bool n m t).
  generalize (n - m).
  intros.
  subst.
  rewrite rewrite_size_eq.
  rewrite t2l_l2t.
  reflexivity.
Qed.

Definition next_tuple (n: nat) (t: n_tuple bool n) : n_tuple bool n.
Proof.
  revert t.
  induction n; simpl; intros t; destruct t.
  - exact tt.
  - destruct b eqn:?.
    + exact (IHn n0, false).
    + exact (n0, true).
Defined.

Fixpoint enum_tuples' {n: nat} k (t: n_tuple bool n) :=
  match k with
  | 0 => nil
  | S k => t :: enum_tuples' k (next_tuple n t)
  end.

Fixpoint enum_tuples (n: nat) : list (n_tuple bool n) :=
  match n with
  | 0 => tt :: nil
  | S n =>
    let shorter := enum_tuples n in
    map (fun t => (t, false)) shorter ++
    map (fun t => (t, true)) shorter
  end.

Lemma length_enum_tuples:
  forall n,
    length (enum_tuples n) = Nat.pow 2 n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite app_length.
    repeat rewrite map_length.
    repeat rewrite IHn.
    Lia.lia.
Qed.

Fixpoint code (n: nat) : n_tuple bool n -> nat :=
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

Global Program Instance BoolTupleFinite (n: nat): Finite (n_tuple bool n) :=
  {| enum := enum_tuples n |}.
Next Obligation.
  induction n.
  - simpl.
    constructor.
    + intro; contradiction.
    + constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map; auto.
      intros; congruence.
    + apply NoDup_map; auto.
      intros; congruence.
    + intros; intro.
      rewrite in_map_iff in *.
      destruct H as [x0 [? _]], H0 as [x1 [? _]].
      congruence.
    + intros; intro.
      rewrite in_map_iff in *.
      destruct H as [x0 [? _]], H0 as [x1 [? _]].
      congruence.
Qed.
Next Obligation.
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

Lemma t2l_eq:
  forall n m (ys : n_tuple bool m) (xs : n_tuple bool n),
    t2l xs = t2l ys ->
    xs ~= ys.
Proof.
  intros.
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
Qed.

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

Lemma t2l_concat:
  forall n m (xs: n_tuple bool n) (ys: n_tuple bool m),
    t2l (n_tuple_concat xs ys) = t2l xs ++ t2l ys.
Proof.
  intros.
  replace (t2l (n_tuple_concat xs ys)) with (t2l (n_tuple_concat' xs ys))
    by (eapply t2l_proper; symmetry; eapply concat_concat').
  apply t2l_concat'.
Qed.

Lemma n_tuple_concat_roundtrip:
  forall n m (t: n_tuple bool m),
    JMeq (n_tuple_concat (n_tuple_take_n n t) (n_tuple_skip_n n t)) t.
Proof.
  intros.
  unfold n_tuple_concat.
  rewrite rewrite_size_jmeq.
  apply t2l_eq.
  rewrite t2l_concat'.
  rewrite t2l_n_tuple_take_n, t2l_n_tuple_skip_n.
  apply List.firstn_skipn.
Admitted.

Lemma n_tuple_take_n_roundtrip:
  forall n (t: n_tuple bool n) k (t': n_tuple bool k),
    t ~= n_tuple_take_n n (n_tuple_concat t t')
.
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

Lemma n_tuple_skip_n_roundtrip:
  forall n (t: n_tuple bool n) k (t': n_tuple bool k),
    t' ~= n_tuple_skip_n n (n_tuple_concat t t')
.
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
Qed.
