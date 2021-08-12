Require Import Coq.Lists.List.
Import ListNotations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.

Print conf_rel.

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
  | ConfigPair (n m: nat).

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | KeyLit: forall n, H n -> funs [] (Key n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo,
      funs [Bits n] (Bits (1 + hi - lo))
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
  Definition tms ctx := FirstOrder.tms sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | State => states (P4A.interp a) + bool
    | Store => store (P4A.interp a)
    | Key n => H n
    | ConfigPair n m => conf * conf
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
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (KeyLit k) hnil := k;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_app xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup n) (store ::: k ::: hnil) :=
        match P4A.find (P4A.HRVar (existT _ n k)) store with 
        | P4A.VBits v => v
        end;
      mod_fns (Update n) (store ::: k ::: v ::: hnil) :=
        P4A.assign (P4A.HRVar k) (P4A.VBits (t2l _ _ v)) store;
      mod_fns (State1 _ _) ((q1, q2) ::: hnil) := fst (fst q1);
      mod_fns (Store1 _ _) ((q1, q2) ::: hnil) := snd (fst q1);
      mod_fns (State2 _ _) ((q1, q2) ::: hnil) := fst (fst q2);
      mod_fns (Store2 _ _) ((q1, q2) ::: hnil) := snd (fst q2);
      mod_fns (Buf1 _ _) ((q1, q2) ::: hnil) := snd (snd q1);
      mod_fns (Buf2 _ _) ((q2, q2) ::: hnil) := snd (snd q2)
    }.

  Fixpoint tr_bctx (b: bctx): ctx sig :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (tr_bctx b) (Bits size)
    end.

  Definition l2t {A} (l: list A) : n_tuple A (List.length l).
  Admitted.

  Definition be_sort {c} (b1 b2 h) (e: bit_expr H c) :=
    match e with
    | BELit _ _ l => Bits (List.length l)
    | BEBuf a => Bits b1
    | BEHdr a h => 
    | BEVar b => _
    | BESlice e hi lo => _
    | BEConcat e1 e2 => _

  Fixpoint tr_bit_expr {c} (e: bit_expr H c) : tm sig (tr_bctx c) (be_sort e) :=
    match e with
    | BELit _ _ l => TFun _ _ _ (BitsLit (List.length l) (l2t l))
    | BEBuf a => _
    | BEHdr a h => _
    | BEVar b => _
    | BESlice e hi lo => _
    | BEConcat e1 e2 => _
    end.

End AutModel.
