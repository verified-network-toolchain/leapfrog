Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.JMeq.
Require Import Coq.Init.Peano.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.EquivDec.
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
  induction n; cbn; destruct t.
  - reflexivity.
  - rewrite IHn.
    reflexivity.
Qed.

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
Qed.

Lemma concat'_cons:
  forall A n m (xs: n_tuple A n) (ys: n_tuple A m) a,
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
Qed.

Lemma concat_cons:
  forall bool n m (xs: n_tuple bool n) (ys: n_tuple bool m) a,
    JMeq (n_tuple_cons (n_tuple_concat xs ys) a)
         (n_tuple_concat (n_tuple_cons xs a) ys).
Proof.
  intros.
  unfold n_tuple_concat.
  generalize (n_tuple_concat_obligation_1 bool (1 + n) m).
  generalize (n_tuple_concat_obligation_1 bool n m).
  intros e e0.
  rewrite e, e0.
  replace (rewrite_size eq_refl _) with (n_tuple_concat' xs ys).
  replace (rewrite_size eq_refl _) with (n_tuple_concat' (n_tuple_cons xs a) ys).
  - now rewrite concat'_cons.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
  - apply JMeq_eq.
    now rewrite rewrite_size_jmeq.
Qed.

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
      apply concat_cons.
  Qed.

  Lemma l2t_snoc:
    forall (l: list A) (x: A),
      JMeq (l2t (l ++ [x])) (l2t l, x).
  Proof.
  Admitted.

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
