From Equations Require Import Equations.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Import FirstOrder.

Section StageOne.
  Set Implicit Arguments.
  Set Universe Polymorphism.
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

  Fixpoint tr_bctx (b: bctx): ctx (sig a) :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (tr_bctx b) (Bits size)
    end.

  Fixpoint app_ctx {s} (c1 c2: ctx s): ctx s :=
    match c2 with
    | CEmp _ => c1
    | CSnoc _ c2' sort =>
      CSnoc _ (app_ctx c1 c2') sort
    end.

  Definition weaken_var_one {s: signature} {sort: s.(sig_sorts)}
             {c: ctx s} (sort': s.(sig_sorts)) (v: var s c sort)
    : var s (CSnoc _ c sort') sort :=
    VThere s _ _ _ v.

  Equations weaken_var {s: signature} {sort: s.(sig_sorts)}
             {c1: ctx s} (c2: ctx s) (v: var s c1 sort)
    : var s (app_ctx c1 c2) sort :=
    { weaken_var (CEmp _) v := v;
      weaken_var (CSnoc _ c2' sort') v := VThere s _ _ _ (weaken_var c2' v) }.

  Definition be_sort {c} b1 b2 (e: bit_expr H c) : sorts :=
    Bits (be_size b1 b2 e).

  Fixpoint reindex_var {s: signature} {c c': ctx s} {sort} (v: var _ c' sort) : var _ (app_ctx c c') sort :=
  match v in (var _ c0 s0) return (var s (app_ctx c c0) s0) with
  | VHere _ ctx s0 => VHere s (app_ctx c ctx) s0
  | VThere _ ctx s0 s' v0 => VThere s (app_ctx c ctx) s0 s' (reindex_var v0)
  end.

  Equations tr_var {c: bctx} (x: bvar c) : var (sig a) (tr_bctx c) (Bits (check_bvar x)) :=
    { tr_var (BVarTop c size) :=
        VHere _ (tr_bctx c) (Bits (check_bvar (BVarTop c size)));
      tr_var (BVarRest y) :=
        VThere _ (tr_bctx _) _ (Bits (check_bvar y)) (tr_var y) }.

  Equations tr_bit_expr
            {c: bctx}
            {c': ctx (sig a)}
            (b1 b2: nat)
            (q: tm (sig a) (app_ctx c' (tr_bctx c)) (ConfigPair b1 b2))
            (e: bit_expr H c)
    : tm (sig a) (app_ctx c' (tr_bctx c)) (be_sort b1 b2 e) :=
    { tr_bit_expr q (BELit _ _ l) :=
        TFun (sig a) (BitsLit a (List.length l) (l2t l)) TSNil;
      tr_bit_expr q (BEBuf _ _ Left) :=
        TFun (sig a) (Buf1 _ b1 b2) (TSCons q TSNil);
      tr_bit_expr q (BEBuf _ _ Right) :=
        TFun (sig a) (Buf2 _ b1 b2) (TSCons q TSNil);
      tr_bit_expr q (@BEHdr H _ Left (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit a _ (projT2 h)) TSNil in
        let store := TFun (sig a) (Store1 a b1 b2) (TSCons q TSNil) in
        TFun (sig a) (Lookup a (projT1 h)) (TSCons store (TSCons key TSNil));
      tr_bit_expr q (BEHdr _ Right (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit a _ (projT2 h)) TSNil in
        let store := TFun (sig a) (Store2 a b1 b2) (TSCons q TSNil) in
        TFun (sig a) (Lookup a (projT1 h)) (TSCons store (TSCons key TSNil));
      tr_bit_expr q (BEVar _ b) :=
        TVar (reindex_var (tr_var b));
      tr_bit_expr q (BESlice e hi lo) :=
        TFun (sig a) (Slice a _ hi lo) (TSCons (tr_bit_expr q e) TSNil);
      tr_bit_expr q (BEConcat e1 e2) :=
        TFun (sig a) (Concat _ _ _) (TSCons (tr_bit_expr q e1) (TSCons (tr_bit_expr q e2) TSNil)) }.

  Equations tr_store_rel
            {c: bctx}
            {c': ctx (sig a)}
            (b1 b2: nat)
            (q: tm (sig a) (app_ctx c' (tr_bctx c)) (ConfigPair b1 b2))
            (r: store_rel H c)
            : fm (sig a) (app_ctx c' (tr_bctx c)) :=
    { tr_store_rel q BRTrue := FTrue;
      tr_store_rel q BRFalse := FFalse;
      tr_store_rel q (BREq e1 e2) :=
        match eq_dec (be_size b1 b2 e1) (be_size b1 b2 e2) with
        | left Heq =>
          FEq (eq_rect _ (fun n => tm (sig a) _ (Bits n))
                       (tr_bit_expr q e1) _ Heq)
              (tr_bit_expr q e2)
        | right _ => FFalse
        end;
      tr_store_rel q (BRAnd r1 r2) :=
        FAnd _ (tr_store_rel q r1)
               (tr_store_rel q r2);
      tr_store_rel q (BROr r1 r2) :=
        FOr _ (tr_store_rel q r1)
              (tr_store_rel q r2);
      tr_store_rel q (BRImpl r1 r2) :=
        FOr _ (FNeg _ (tr_store_rel q r1))
              (tr_store_rel q r2)
    }.

  Fixpoint quantify {s} {c0: ctx s} (c: ctx s): fm s (app_ctx c0 c) -> fm s c0 :=
    match c as c' return fm s (app_ctx c0 c') -> fm s c0 with
    | CEmp _ => fun f => f
    | CSnoc _ c' sort => fun f => quantify c' (FForall _ f)
    end.

  Definition FImpl {s c} (f1 f2: fm s c) :=
    FOr _ (FNeg _ f1) f2.

  Definition tr_conf_rel (r: conf_rel S H) : fm (sig a) (CEmp _) :=
    let s1 := r.(cr_st).(cs_st1).(st_state) in
    let b1 := r.(cr_st).(cs_st1).(st_buf_len) in
    let s2 := r.(cr_st).(cs_st2).(st_state) in
    let b2 := r.(cr_st).(cs_st2).(st_buf_len) in
    let qsort: sig_sorts (sig a) := ConfigPair b1 b2 in
    let c' := (CSnoc _ (CEmp _) qsort) in
    let s1eq: fm (sig a) c' :=
        FEq (TFun (sig a) (State1 a b1 b2)
                  (TSCons (TVar (VHere _ _ _)) TSNil))
            (TFun (sig a) (StateLit _ s1) TSNil)
    in
    let s2eq: fm (sig a) c' :=
        FEq (TFun (sig a) (State2 a b1 b2)
                  (TSCons (TVar (VHere _ _ _)) TSNil))
            (TFun (sig a) (StateLit _ s2) TSNil)
    in
    let q: var (sig a) (app_ctx c' (tr_bctx r.(cr_ctx))) qsort :=
        weaken_var _ (VHere _ _ _)
    in
    let sr := quantify _ (tr_store_rel (TVar q) r.(cr_rel)) in
    let f: fm (sig a) (CEmp _) := FForall qsort (FImpl s1eq (FImpl s2eq sr)) in
    f.
