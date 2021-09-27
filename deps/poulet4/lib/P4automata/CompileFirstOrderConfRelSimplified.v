From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Poulet4.P4automata.FirstOrderConfRelSimplified.
Require Poulet4.P4automata.FirstOrderBitVec.
Require Import Poulet4.P4automata.Ntuple.
Import FirstOrder.

Module FOS := FirstOrderConfRelSimplified.
Module FOBV := FirstOrderBitVec.

Section CompileFirstOrderConfRelSimplified.
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

  Equations compile_store_ctx_partial
    (hdrs: list (Syntax.H' H))
    : ctx FOBV.sig
  := {
    compile_store_ctx_partial nil := CEmp _;
    compile_store_ctx_partial (hdr :: hdrs) :=
      CSnoc _ (compile_store_ctx_partial hdrs) (FOBV.Bits (projT1 hdr))
  }.

  Definition compile_store_ctx : ctx FOBV.sig :=
    compile_store_ctx_partial (enum (Syntax.H' H)).

  Equations compile_ctx (c: ctx (FOS.sig H)) : ctx FOBV.sig := {
    compile_ctx (CEmp _) := CEmp _;
    compile_ctx (CSnoc _ c FOS.Store) :=
      app_ctx (compile_ctx c) compile_store_ctx;
    compile_ctx (CSnoc _ c (FOS.Bits n)) :=
      CSnoc _ (compile_ctx c) (FOBV.Bits n);
  }.

  Lemma list_in_excl {X: Type} (x x': X) (l: list X):
    List.In x (x' :: l) ->
    x' <> x ->
    List.In x l.
  Proof.
    intros.
    destruct H0; auto.
    contradiction.
  Qed.

  Definition compile_lookup'
    (k: Syntax.H' H)
    (enum: list (Syntax.H' H))
    (elem_of_enum: List.In k enum)
    : var (FOBV.sig) (compile_store_ctx_partial enum) (FOBV.Bits (projT1 k)).
  Proof.
    induction enum.
    - contradiction.
    - autorewrite with compile_store_ctx_partial.
      destruct (equiv_dec k a0).
      + rewrite e.
        apply VHere.
      + apply VThere.
        apply IHenum.
        apply list_in_excl with (x' := a0); auto.
  Defined.

  Definition compile_lookup (k: Syntax.H' H)
    : var FOBV.sig compile_store_ctx (FOBV.Bits (projT1 k))
  :=
    compile_lookup' k (enum (Syntax.H' H)) (elem_of_enum k).

  Equations tm_cons {c s' s}
    (t: tm FOBV.sig c s)
    : tm FOBV.sig (CSnoc _ c s') s := {
    tm_cons (TVar v) := TVar (VThere _ _ _ _ v);
    tm_cons (TFun _ fn args) := TFun _ fn (tms_cons args);
  } where tms_cons {c s' s}
    (ts: HList.t (tm FOBV.sig c) s)
    : HList.t (tm FOBV.sig (CSnoc _ c s')) s := {
    tms_cons (HList.HNil _) := (HList.HNil _);
    tms_cons (HList.HCons _ t ts) :=
      HList.HCons _ (tm_cons t) (tms_cons ts);
  }.

  Definition compile_sizes (enum: list (Syntax.H' H)): nat :=
    let sizes := List.map (@projT1 nat H) enum in
    (* let sizes' := List.filter (fun n => (0 <? n)%nat) sizes in  *)
    List.fold_right Nat.add 0 sizes.

  Definition compile_sort (s: FOS.sorts) : FOBV.sorts :=
    match s with
    | FOS.Bits n => FOBV.Bits n
    | FOS.Store => FOBV.Bits (compile_sizes (enum (Syntax.H' H)))
    end.

  Equations compile_store'
    (enum: list (Syntax.H' H))
    : tm FOBV.sig (compile_store_ctx_partial enum)
                  (FOBV.Bits (compile_sizes enum)) := {
    compile_store' nil := TFun FOBV.sig (FOBV.BitsLit 0 tt) (HList.HNil _);
    compile_store' (elem :: enum) :=
      TFun FOBV.sig (FOBV.Concat (projT1 elem) (compile_sizes enum))
                    (HList.HCons _ (TVar (VHere _ _ _))
                    (HList.HCons _ (tm_cons (compile_store' enum))
                    (HList.HNil _)));
  }.

  Definition compile_store
    : tm (FOBV.sig) compile_store_ctx (compile_sort FOS.Store)
  :=
    compile_store' (enum (Syntax.H' H)).

  Equations subscript {c n}
    (v: var (FOS.sig H) c FOS.Store)
    (v': var FOBV.sig compile_store_ctx (FOBV.Bits n))
    : var FOBV.sig (compile_ctx c) (FOBV.Bits n)
  := {
    subscript (VHere c' _) v' :=
      reindex_var v';
    subscript (VThere _ c (FOS.Bits n) _ v) v' :=
      VThere _ _ _ _ (subscript v v');
    subscript (VThere _ c FOS.Store _ v) v' :=
      weaken_var _ (subscript v v');
  }.

  Equations compile_var
    {c: ctx (FOS.sig H)}
    {s: FOS.sorts}
    (v: var (FOS.sig H) c s)
    : tm FOBV.sig (compile_ctx c) (compile_sort s)
  := {
    compile_var (VHere _ c (FOS.Bits n)) :=
      TVar (VHere _ (compile_ctx c) (FOBV.Bits n));
    compile_var (VHere _ c FOS.Store) := reindex_tm compile_store;
    compile_var (VThere _ c (FOS.Bits _) s' v) := tm_cons (compile_var v);
    compile_var (VThere _ c FOS.Store s' v) := weaken_tm _ (compile_var v);
  }.

  Equations compile_tm
    {c: ctx (FOS.sig H)}
    {s: FOS.sorts}
    (t: tm (FOS.sig H) c s):
    tm FOBV.sig (compile_ctx c) (compile_sort s) := {
    compile_tm (TVar v) := compile_var v;
    compile_tm (TFun _ (FOS.BitsLit _ n v) (HList.HNil _)) :=
      TFun FOBV.sig (FOBV.BitsLit n v) (HList.HNil _);
    compile_tm (TFun _ (FOS.Concat _ n m) (HList.HCons _ t1 (HList.HCons _ t2 (HList.HNil _)))) :=
      TFun FOBV.sig (FOBV.Concat n m) (HList.HCons _ (compile_tm t1) (HList.HCons _ (compile_tm t2) (HList.HNil _)));
    compile_tm (TFun _ (FOS.Slice _ n hi lo) (HList.HCons _ t (HList.HNil _ ))) :=
      TFun FOBV.sig (FOBV.Slice n hi lo) (HList.HCons _ (compile_tm t) (HList.HNil _));
    compile_tm (TFun _ (FOS.Lookup n h) (HList.HCons _ (TVar v) (HList.HNil _))) :=
      TVar (subscript v (compile_lookup (existT H n h)));
  }.

  Equations compile_fm
    {c: ctx (FOS.sig H)}
    (f: fm (FOS.sig H) c)
    : fm FOBV.sig (compile_ctx c) := {
    compile_fm FTrue := FTrue;
    compile_fm FFalse := FFalse;
    compile_fm (FEq t1 t2) := FEq (compile_tm t1) (compile_tm t2);
    compile_fm (FNeg f) := FNeg _ (compile_fm f);
    compile_fm (FOr f1 f2) := FOr _ (compile_fm f2) (compile_fm f2);
    compile_fm (FAnd f1 f2) := FAnd _ (compile_fm f2) (compile_fm f2);
    compile_fm (FImpl f1 f2) := FImpl (compile_fm f2) (compile_fm f2);
    compile_fm (@FForall _ c (FOS.Bits n) f) :=
      FForall (sig := FOBV.sig) (FOBV.Bits n) (compile_fm f);
    compile_fm (@FForall _ c FOS.Store f) :=
      quantify compile_store_ctx (compile_fm f)
  }.

  Lemma compile_simplified_fm_bv_correct:
      forall fm,
        interp_fm (m := FOS.fm_model a) (VEmp _ _) fm <->
        interp_fm (m := FOBV.fm_model) (VEmp _ _) (compile_fm fm)
        .
  Proof.
  Admitted.
End CompileFirstOrderConfRelSimplified.
