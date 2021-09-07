Require Import Coq.Lists.List.
Import ListNotations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.Ntuple.

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

  Notation conf := (configuration (P4A.interp S H a)).

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

  Definition conf' (n: nat) :=
    {c: conf | c.(conf_buf_len _) = n}.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | State => states (P4A.interp S H a) + bool
    | Store => store (P4A.interp S H a)
    | Key n => H n
    | ConfigPair n m => conf' n * conf' m
    end.

  Definition l2t {A} (l: list A) : n_tuple A (List.length l).
  Admitted.

  Definition n_zeroes (n: nat) : n_tuple bool n.
  Admitted.

  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).

  Obligation Tactic := idtac.
  Equations mod_fns
             {params ret}
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (KeyLit k) hnil := k;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup n) (store ::: key ::: hnil) :=
        match P4A.find H key store with
        | Some (P4A.VBits _ v) => v
        | None => n_zeroes n
        end;
      mod_fns (Update n) (store ::: k ::: v ::: hnil) :=
        P4A.assign _ k (P4A.VBits _ v) store;
      mod_fns (State1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_state _);
      mod_fns (Store1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_store _);
      mod_fns (State2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_state _);
      mod_fns (Store2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_store _);
      mod_fns (Buf1 n m) ((q1, q2) ::: hnil) := _;
      mod_fns (Buf2 n m) ((q2, q2) ::: hnil) := _
    }.
  Next Obligation.
    unfold conf'.
    intros.
    pose ((proj1_sig q1).(conf_buf _)).
    destruct q1.
    simpl in *.
    rewrite e in n0.
    exact n0.
  Defined.
  Next Obligation.
    unfold conf'.
    intros.
    pose ((proj1_sig q2).(conf_buf _)).
    destruct q2.
    simpl in *.
    rewrite e in n0.
    exact n0.
  Defined.

  Fixpoint tr_bctx (b: bctx): ctx sig :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (tr_bctx b) (Bits size)
    end.

  Fixpoint be_size {c} b1 b2 (e: bit_expr H c) : nat :=
    match e with
    | BELit _ _ l => List.length l
    | BEBuf _ _ side =>
      match side with
      | Left => b1
      | Right => b2
      end
    | BEHdr _ a (P4A.HRVar h) => projT1 h
    | BEVar _ x => check_bvar x
    | BESlice e hi lo =>
      let n := be_size b1 b2 e in
      Nat.min (1 + hi) n - lo
    | BEConcat e1 e2 =>
      be_size b1 b2 e1 + be_size b1 b2 e2
    end.

  Definition be_sort {c} b1 b2 (e: bit_expr H c) : sorts :=
    Bits (be_size b1 b2 e).
  
  Equations tr_bit_expr {c} b1 b2 (e: bit_expr H c) : tm (tr_bctx c) (be_sort b1 b2 e) :=
    { tr_bit_expr b1 b2 (BELit _ _ l) :=
        TFun sig _ _ _ (BitsLit (List.length l) (l2t l)) (TSNil _ _);
      tr_bit_expr b1 b2 (BEBuf _ _ side) := _;
      tr_bit_expr b1 b2 (BEHdr _ a h) := _;
      tr_bit_expr b1 b2 (BEVar _ b) := _;
      tr_bit_expr b1 b2 (BESlice e hi lo) := _;
      tr_bit_expr b1 b2 (BEConcat e1 e2) := _
    }.

End AutModel.
