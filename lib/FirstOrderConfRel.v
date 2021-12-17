Require Import Coq.Lists.List.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Require Import Leapfrog.Ntuple.

Import ListNotations.
Import HListNotations.

Section AutModel.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (St: Type).
  Context `{St_eq_dec: EquivDec.EqDec St eq}.
  Context `{St_finite: @Finite St _ St_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> nat).

  Variable (a: P4A.t St Hdr_sz).

  Notation conf := (configuration (P4A.interp a)).

  Inductive sorts: Type :=
  | Bits (n: nat)
  | State
  | Store
  | ConfigPair (n m: nat)
  | Natural.

  Definition conf' (n: nat) :=
    {c: conf | c.(conf_buf_len) = n}.

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | StateLit: forall (s: states (P4A.interp a) + bool), funs [] State
  | ConfPairLit: forall n m (c: conf' n * conf' m), funs [] (ConfigPair n m)
  | NatLit: forall n : nat, funs [] Natural
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (Nat.min (1 + hi) n - lo))
  | Lookup: forall k, funs [Store] (Bits (Hdr_sz k))
  | Update: forall k, funs [Store; Bits (Hdr_sz k)] Store
  | State1: forall n m, funs [ConfigPair n m] State
  | Store1: forall n m, funs [ConfigPair n m] Store
  | State2: forall n m, funs [ConfigPair n m] State
  | Store2: forall n m, funs [ConfigPair n m] Store
  | Buf1: forall n m, funs [ConfigPair n m] (Bits n)
  | Buf2: forall n m, funs [ConfigPair n m] (Bits m).

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | State => states (P4A.interp a) + bool
    | Store => store (P4A.interp a)
    | ConfigPair n m => conf' n * conf' m
    | Natural => nat
    end.

  Equations mod_fns
             params ret
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (StateLit s) hnil := s;
      mod_fns (ConfPairLit c) hnil := c;
      mod_fns (NatLit n) hnil := n;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup k) (store ::: hnil) :=
        match P4A.find Hdr Hdr_sz k store with
        | P4A.VBits _ v => v
        end;
      mod_fns (Update k) (store ::: v ::: hnil) :=
        P4A.assign Hdr Hdr_sz k (P4A.VBits _ v) store;
      mod_fns (State1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_state);
      mod_fns (Store1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_store);
      mod_fns (State2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_state);
      mod_fns (Store2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_store);
      mod_fns (Buf1 n m) ((q1, q2) ::: hnil) :=
        eq_rect _ _ (proj1_sig q1).(conf_buf) _ (proj2_sig q1);
      mod_fns (Buf2 n m) ((q2, q2) ::: hnil) :=
        eq_rect _ _ (proj1_sig q2).(conf_buf) _ (proj2_sig q2)
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.
End AutModel.
