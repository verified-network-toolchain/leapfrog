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

Fixpoint t2l A (n: nat) (x: n_tuple A n) : list A :=
  match n as n' return n_tuple A n' -> list A with
  | 0 => fun _ => nil
  | S n => fun p => t2l A n (fst p) ++ [snd p]
  end x.

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

Definition n_tuple_take_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (Nat.min n m).
Admitted.
Definition n_tuple_skip_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (m - n).
Admitted.
Definition n_tuple_slice {A n} (hi lo: nat) (xs: n_tuple A n) : n_tuple A (Nat.min (1 + hi) n - lo).
Admitted.
