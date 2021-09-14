Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Import ListNotations.

Fixpoint n_tuple A (n: nat): Type :=
  match n with
  | 0 => unit
  | S n => n_tuple A n * A
  end.

Fixpoint n_tuple_app {A n} (xs: n_tuple A n) (x: A) : n_tuple A (n + 1) :=
  match n as n' return (n_tuple A n' -> n_tuple A (n' + 1)) with
  | 0 =>
    fun _ => (tt, x)
  | S n =>
    fun '(xs, x') => (n_tuple_app xs x, x')
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


Definition l2t {A: Type} (xs: list A) : n_tuple A (length xs).
induction xs.
- exact tt.
- unfold length. fold (length xs). 
  pose (ret := n_tuple_app IHxs a).
  erewrite <- plus_n_Sm in ret.
  erewrite <- plus_n_O in ret.
  exact ret.
Defined.

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

Definition n_tuple_concat {A n m} (xs: n_tuple A n) (ys: n_tuple A m) : n_tuple A (n + m).
  rewrite Plus.plus_comm.
  exact (n_tuple_concat' xs ys).
Defined.

Program Instance n_tuple_eq_dec
         {A: Type}
         `{A_eq_dec: EquivDec.EqDec A eq}
         (n: nat) : EquivDec.EqDec (n_tuple A n) eq.
Next Obligation.
Admitted.

Require Import Coq.Init.Peano.
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

Require Import Coq.Lists.List.

Definition n_tuple_take_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (Nat.min n m). 
pose (ret := l2t (firstn n (t2l xs))).
erewrite firstn_length in ret.
erewrite t2l_len in ret.
exact ret.
Defined.

Definition n_tuple_skip_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (m - n).
pose (ret := l2t (skipn n (t2l xs))).
erewrite skipn_length in ret.
erewrite t2l_len in ret.
exact ret.
Defined.

Program Definition n_tuple_slice {A n} (hi lo: nat) (xs: n_tuple A n) : n_tuple A (Nat.min (1 + hi) n - lo) :=
  n_tuple_take_n (hi - lo) (n_tuple_skip_n (hi - n) xs).
Admit Obligations.
