Require Import Coq.Lists.List.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.Ntuple.

Import ListNotations.
Import HListNotations.

Section AutModel.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Inductive sorts: Type :=
  | Bits (n: nat)
  | State
  | Store
  | Key (n: nat)
  | ConfigPair (n m: nat)
  | Natural.

  Definition conf' (n: nat) :=
    {c: conf | c.(conf_buf_len) = n}.

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | KeyLit: forall n, H n -> funs [] (Key n)
  | StateLit: forall (s: states (P4A.interp a) + bool), funs [] State
  | ConfPairLit: forall n m (c: conf' n * conf' m), funs [] (ConfigPair n m)
  | NatLit: forall n : nat, funs [] Natural
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (Nat.min (1 + hi) n - lo))
  | Lookup: forall n, funs [Store; Key n] (Bits n)
  | Update: forall n, funs [Store; Key n; Bits n] Store
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
    | Key n => H n
    | ConfigPair n m => conf' n * conf' m
    | Natural => nat
    end.

  Obligation Tactic := idtac.
  Equations mod_fns
             params ret
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (KeyLit k) hnil := k;
      mod_fns (StateLit s) hnil := s;
      mod_fns (ConfPairLit c) hnil := c;
      mod_fns (NatLit n) hnil := n;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup n) (store ::: key ::: hnil) :=
        match P4A.find H key store with
        | P4A.VBits _ v => v
        end;
      mod_fns (Update n) (store ::: k ::: v ::: hnil) :=
        P4A.assign _ k (P4A.VBits _ v) store;
      mod_fns (State1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_state);
      mod_fns (Store1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_store);
      mod_fns (State2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_state);
      mod_fns (Store2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_store);
      mod_fns (Buf1 n m) ((q1, q2) ::: hnil) :=
        eq_rect _ _ (proj1_sig q1).(conf_buf) _ (proj2_sig q1);
      mod_fns (Buf2 n m) ((q2, q2) ::: hnil) :=
        eq_rect _ _ (proj1_sig q2).(conf_buf) _ (proj2_sig q2);
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
