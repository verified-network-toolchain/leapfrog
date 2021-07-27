Require Import Coq.Lists.List.
Import ListNotations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.

Print conf_rel.

Inductive sorts: Type :=
| Bits (n: nat)
| State
| Store
| Key
| ConfigPair.

Inductive funs: arity sorts -> sorts -> Type :=
| Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
| Slice: forall n hi lo,
    n > hi ->
    hi > lo ->
    funs [Bits n] (Bits (1 + hi - lo))
| Update: forall n, funs [Store; Key; Bits n] Store
| State1: funs [ConfigPair] State
| Store1: funs [ConfigPair] Store
| State2: funs [ConfigPair] State
| Store2: funs [ConfigPair] Store.

(* I'm making the buffers relations which have to be constrained with
   axioms because they might return (Bits n) for any n. *)
Inductive rels: arity sorts -> Type :=
| Buf1: forall n, rels [ConfigPair; (Bits n)]
| Buf2: forall n, rels [ConfigPair; (Bits n)]
| Lookup: forall n, rels [Store; Key; Bits n].

Definition sig: signature :=
  {| sig_sorts := sorts;
     sig_funs := funs;
     sig_rels := rels |}.

Section AutModel.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | State => states (P4A.interp a) + bool
    | Store => store (P4A.interp a)
    | Key => H
    | ConfigPair => conf * conf
    end.

  Definition n_tuple_take_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (Nat.min n m).
  Admitted.
  Definition n_tuple_skip_n {A m} (n: nat) (xs: n_tuple A m) : n_tuple A (m - n).
  Admitted.
  Definition n_tuple_slice {A n} (hi lo: nat) (xs: n_tuple A n) : n_tuple A (1 + hi - lo).
  Admitted.

  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).

  Equations mod_fns
             {params ret}
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_app xs ys;
      mod_fns (Slice n hi lo Hn Hhi) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Update n) (store ::: k ::: v ::: hnil) :=
        P4A.assign (P4A.HRVar k) (P4A.VBits (t2l _ _ v)) store;
      mod_fns State1 ((q1, q2) ::: hnil) := fst (fst q1);
      mod_fns Store1 ((q1, q2) ::: hnil) := snd (fst q1);
      mod_fns State2 ((q1, q2) ::: hnil) := fst (fst q2);
      mod_fns Store2 ((q1, q2) ::: hnil) := snd (fst q2)
    }.
End AutModel.
