From Equations Require Import Equations.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Import FirstOrder.

Section CompileConfRel.
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

  Fixpoint compile_bctx (b: bctx): ctx (sig a) :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (compile_bctx b) (Bits size)
    end.

  Definition be_sort {c} b1 b2 (e: bit_expr H c) : sorts :=
    Bits (be_size b1 b2 e).

  Equations compile_var {c: bctx} (x: bvar c) : var (sig a) (compile_bctx c) (Bits (check_bvar x)) :=
    { compile_var (BVarTop c size) :=
        VHere _ (compile_bctx c) (Bits (check_bvar (BVarTop c size)));
      compile_var (BVarRest y) :=
        VThere _ (compile_bctx _) _ (Bits (check_bvar y)) (compile_var y) }.

  Equations compile_bit_expr
            {c: bctx}
            {c': ctx (sig a)}
            (b1 b2: nat)
            (q: tm (sig a) (app_ctx c' (compile_bctx c)) (ConfigPair b1 b2))
            (e: bit_expr H c)
    : tm (sig a) (app_ctx c' (compile_bctx c)) (be_sort b1 b2 e) :=
    { compile_bit_expr q (BELit _ _ l) :=
        TFun (sig a) (BitsLit a (List.length l) (l2t l)) TSNil;
      compile_bit_expr q (BEBuf _ _ Left) :=
        TFun (sig a) (Buf1 _ b1 b2) (TSCons q TSNil);
      compile_bit_expr q (BEBuf _ _ Right) :=
        TFun (sig a) (Buf2 _ b1 b2) (TSCons q TSNil);
      compile_bit_expr q (@BEHdr H _ Left (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit a _ (projT2 h)) TSNil in
        let store := TFun (sig a) (Store1 a b1 b2) (TSCons q TSNil) in
        TFun (sig a) (Lookup a (projT1 h)) (TSCons store (TSCons key TSNil));
      compile_bit_expr q (BEHdr _ Right (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit a _ (projT2 h)) TSNil in
        let store := TFun (sig a) (Store2 a b1 b2) (TSCons q TSNil) in
        TFun (sig a) (Lookup a (projT1 h)) (TSCons store (TSCons key TSNil));
      compile_bit_expr q (BEVar _ b) :=
        TVar (reindex_var (compile_var b));
      compile_bit_expr q (BESlice e hi lo) :=
        TFun (sig a) (Slice a _ hi lo) (TSCons (compile_bit_expr q e) TSNil);
      compile_bit_expr q (BEConcat e1 e2) :=
        TFun (sig a) (Concat _ _ _) (TSCons (compile_bit_expr q e1) (TSCons (compile_bit_expr q e2) TSNil)) }.

  Equations compile_store_rel
            {c: bctx}
            {c': ctx (sig a)}
            (b1 b2: nat)
            (q: tm (sig a) (app_ctx c' (compile_bctx c)) (ConfigPair b1 b2))
            (r: store_rel H c)
            : fm (sig a) (app_ctx c' (compile_bctx c)) :=
    { compile_store_rel q BRTrue := FTrue;
      compile_store_rel q BRFalse := FFalse;
      compile_store_rel q (BREq e1 e2) :=
        match eq_dec (be_size b1 b2 e1) (be_size b1 b2 e2) with
        | left Heq =>
          FEq (eq_rect _ (fun n => tm (sig a) _ (Bits n))
                       (compile_bit_expr q e1) _ Heq)
              (compile_bit_expr q e2)
        | right _ => FFalse
        end;
      compile_store_rel q (BRAnd r1 r2) :=
        FAnd _ (compile_store_rel q r1)
               (compile_store_rel q r2);
      compile_store_rel q (BROr r1 r2) :=
        FOr _ (compile_store_rel q r1)
              (compile_store_rel q r2);
      compile_store_rel q (BRImpl r1 r2) :=
        FOr _ (FNeg _ (compile_store_rel q r1))
              (compile_store_rel q r2)
    }.

  Definition compile_conf_rel
    {c': ctx (sig a)}
    (r: conf_rel S H)
    (q1 q2: conf)
    : fm (sig a) c'
  :=
    let s1 := r.(cr_st).(cs_st1).(st_state) in
    let s2 := r.(cr_st).(cs_st2).(st_state) in
    let q1' : conf' a q1.(conf_buf_len) :=
        exist (fun c => c.(conf_buf_len) = q1.(conf_buf_len)) q1 eq_refl in
    let q2' : conf' a q2.(conf_buf_len) :=
        exist (fun c => c.(conf_buf_len) = q2.(conf_buf_len)) q2 eq_refl in
    (* Same expression twice for type inference to work out. *)
    let lit := TFun (sig a) (ConfPairLit (q1', q2')) TSNil in
    let lit' := TFun (sig a) (ConfPairLit (q1', q2')) TSNil in
    let s1eq :=
        FEq (TFun (sig a) (State1 a q1.(conf_buf_len) q2.(conf_buf_len))
                  (TSCons lit TSNil))
            (TFun (sig a) (StateLit _ s1) TSNil)
    in
    let s2eq :=
        FEq (TFun (sig a) (State2 a q1.(conf_buf_len) q2.(conf_buf_len))
                  (TSCons lit TSNil))
            (TFun (sig a) (StateLit _ s1) TSNil)
    in
    let sr := quantify _ (compile_store_rel lit' r.(cr_rel)) in
    (FImpl s1eq (FImpl s2eq sr)).

  Lemma compile_conf_rel_correct (r: conf_rel S H):
    forall q1 q2,
      interp_conf_rel a r q1 q2 <->
      interp_fm (m := fm_model a) (VEmp _ _) (compile_conf_rel r q1 q2).
  Admitted.
End CompileConfRel.
