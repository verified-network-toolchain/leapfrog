Require Import Coq.Lists.List.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Require Import Leapfrog.Ntuple.

Import ListNotations.
Import HListNotations.

Section FirstOrderBitVec.
  Set Implicit Arguments.

  Inductive sorts: Type :=
  | Bits (n: nat).

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (Nat.min (1 + hi) n - lo)).

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  (* Locate FirstOrder.fm. *)

  Definition fm ctx := fm sig ctx.
  Definition tm ctx := tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    end.

  Obligation Tactic := idtac.
  Equations mod_fns
             params ret
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  (* Instantiation of abstract first-order logic to FOL(BV). *)
  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.
End FirstOrderBitVec.


(* Require Import MirrorSolve.SMT.

Local Declare ML Module "mirrorsolve". *)

(* RegisterSMTSort @Bits @SBitVector. *)

(* RegisterSMTFun Z.Plus "+" 2.
RegisterSMTFun Z.Gte ">=" 2.
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.
RegisterSMTFun Z.Lte "<=" 2.

RegisterSMTBuiltin Z.BLit BoolLit.
RegisterSMTBuiltin Z.ZLit IntLit.

Register FOBV.Bits as p4a.sorts.bits.

Register FOBV.BitsLit as p4a.funs.bitslit.
Register FOBV.Concat as p4a.funs.concat.
Register FOBV.Slice as p4a.funs.slice. *)