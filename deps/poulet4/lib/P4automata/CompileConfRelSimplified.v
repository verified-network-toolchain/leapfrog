From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrderConfRelSimplified.
Require Import Poulet4.P4automata.Ntuple.
Import FirstOrder.

Section CompileConfRelSimplified.
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

  Definition compile_bval {c: bctx} (v: bval c) : valu _ (fm_model a) (compile_bctx c).
  Admitted.

  Definition decompile_val {c: bctx} (v: valu _ (fm_model a) (compile_bctx c)) : bval c.
  Admitted.

  Lemma bval_roundtrip:
    forall {c: bctx} (valu: _ (fm_model a) (compile_bctx c)),
      compile_bval (decompile_val valu) = valu.
  Proof.
  Admitted.

  Equations compile_bit_expr
            {c: bctx}
            {b1 b2: nat}
            (buf1: tm (sig a) (compile_bctx c) (Bits b1))
            (buf2: tm (sig a) (compile_bctx c) (Bits b2))
            (store1 store2: tm (sig a) (compile_bctx c) Store)
            (e: bit_expr H c)
    : tm (sig a) (compile_bctx c) (be_sort b1 b2 e) :=
    { compile_bit_expr buf1 buf2 store1 store2 (BELit _ _ l) :=
        TFun (sig a) (BitsLit _ (List.length l) (Ntuple.l2t l)) TSNil;
      compile_bit_expr buf1 buf2 store1 store2 (BEBuf _ _ Left) := buf1;
      compile_bit_expr buf1 buf2 store1 store2 (BEBuf _ _ Right) := buf2;
      compile_bit_expr buf1 buf2 store1 store2 (@BEHdr H _ Left (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit _ _ (projT2 h)) TSNil in
        TFun (sig a) (Lookup _ (projT1 h)) (TSCons store1 (TSCons key TSNil));
      compile_bit_expr buf1 buf2 store1 store2 (BEHdr _ Right (P4A.HRVar h)) :=
        let key := TFun (sig a) (KeyLit _ _ (projT2 h)) TSNil in
        TFun (sig a) (Lookup _ (projT1 h)) (TSCons store2 (TSCons key TSNil));
      compile_bit_expr buf1 buf2 store1 store2 (BEVar _ b) :=
        TVar (compile_var b);
      compile_bit_expr buf1 buf2 store1 store2 (BESlice e hi lo) :=
        TFun (sig a) (Slice _ _ hi lo)
             (TSCons (compile_bit_expr buf1 buf2 store1 store2 e) TSNil);
      compile_bit_expr buf1 buf2 store1 store2 (BEConcat e1 e2) :=
        TFun (sig a) (Concat _ _ _)
             (TSCons (compile_bit_expr buf1 buf2 store1 store2 e1)
             (TSCons (compile_bit_expr buf1 buf2 store1 store2 e2) TSNil)) }.

  Equations compile_store_rel
            {c: bctx}
            {b1 b2: nat}
            (buf1: tm (sig a) (compile_bctx c) (Bits b1))
            (buf2: tm (sig a) (compile_bctx c) (Bits b2))
            (store1 store2: tm (sig a) (compile_bctx c) Store)
            (r: store_rel H c)
            : fm (sig a) (compile_bctx c) :=
    { compile_store_rel buf1 buf2 store1 store2 BRTrue := FTrue;
      compile_store_rel buf1 buf2 store1 store2 BRFalse := FFalse;
      compile_store_rel buf1 buf2 store1 store2 (BREq e1 e2) :=
        match eq_dec (be_size b1 b2 e1) (be_size b1 b2 e2) with
        | left Heq =>
          FEq (eq_rect _ (fun n => tm (sig a) _ (Bits n))
                       (compile_bit_expr buf1 buf2 store1 store2 e1) _ Heq)
              (compile_bit_expr buf1 buf2 store1 store2 e2)
        | right _ => FFalse
        end;
      compile_store_rel buf1 buf2 store1 store2 (BRAnd r1 r2) :=
        FAnd _ (compile_store_rel buf1 buf2 store1 store2 r1)
               (compile_store_rel buf1 buf2 store1 store2 r2);
      compile_store_rel buf1 buf2 store1 store2 (BROr r1 r2) :=
        FOr _ (compile_store_rel buf1 buf2 store1 store2 r1)
              (compile_store_rel buf1 buf2 store1 store2 r2);
      compile_store_rel buf1 buf2 store1 store2 (BRImpl r1 r2) :=
        FOr _ (FNeg _ (compile_store_rel buf1 buf2 store1 store2 r1))
              (compile_store_rel buf1 buf2 store1 store2 r2)
    }.

  Definition compile_simplified_conf_rel
    {b1 b2: nat}
    (r: simplified_conf_rel H)
    (buf1: tm (sig a) (CEmp _) (Bits b1))
    (buf2: tm (sig a) (CEmp _) (Bits b2))
    (store1 store2: tm (sig a) (CEmp _) Store)
    : fm (sig a) (CEmp _)
  :=
    let sr: fm (sig a) _ :=
        (compile_store_rel (reindex_tm buf1)
                           (reindex_tm buf2)
                           (reindex_tm store1)
                           (reindex_tm store2)
                           (projT2 r))
    in
    quantify_all _ sr.

  Definition compile_simplified_crel
    {b1 b2: nat}
    (R: simplified_crel H)
    (buf1: tm (sig a) (CEmp _) (Bits b1))
    (buf2: tm (sig a) (CEmp _) (Bits b2))
    (store1 store2: tm (sig a) (CEmp _) Store)
    : fm (sig a) (CEmp _) :=
    List.fold_right (fun r f =>
      FAnd _ (compile_simplified_conf_rel r buf1 buf2 store1 store2) f
    ) FTrue R.

  Definition compile_simplified_entailment
    (se: simplified_entailment a)
    (buf1: tm (sig a) (CEmp _) (Bits se.(se_st).(cs_st1).(st_buf_len)))
    (buf2: tm (sig a) (CEmp _) (Bits se.(se_st).(cs_st2).(st_buf_len)))
    (store1 store2: tm (sig a) (CEmp _) Store)
    : fm (sig a) (CEmp _) :=
    (FImpl (compile_simplified_crel se.(se_prems) buf1 buf2 store1 store2)
           (compile_simplified_conf_rel se.(se_concl) buf1 buf2 store1 store2)).

  Definition compile_buf
    {c': ctx (sig a)}
    {n: nat}
    (buf: n_tuple bool n)
    : tm (sig a) c' (Bits n) :=
    TFun (sig a) (BitsLit _ _ buf) TSNil.

  Definition compile_store
    {c': ctx (sig a)}
    (store: store (P4A.interp a))
    : tm (sig a) c' Store :=
    TFun (sig a) (StoreLit store) TSNil.

  Lemma compile_store_rel_correct:
    forall c (r: store_rel H c) valu b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2) store1 store2,
      interp_simplified_store_rel r valu buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (compile_bval valu)
                (compile_store_rel (compile_buf buf1)
                                   (compile_buf buf2)
                                   (compile_store store1)
                                   (compile_store store2) r).
  Proof.
  Admitted.

  Lemma compile_simplified_conf_rel_correct:
    forall r b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2) store1 store2,
      interp_simplified_conf_rel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (VEmp _ _)
                (compile_simplified_conf_rel r
                  (compile_buf buf1)
                  (compile_buf buf2)
                  (compile_store store1)
                  (compile_store store2)).
  Proof.
  Admitted.

  Lemma compile_crel_correct:
    forall r b1 b2 (buf1: n_tuple bool b1) (buf2: n_tuple bool b2) store1 store2,
      interp_simplified_crel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (VEmp _ _)
                (compile_simplified_crel r
                  (compile_buf buf1)
                  (compile_buf buf2)
                  (compile_store store1)
                  (compile_store store2)).
  Proof.
  Admitted.

  Lemma compile_simplified_entailment_correct:
      forall e,
        interp_simplified_entailment e <->
        forall buf1 buf2 store1 store2,
          interp_fm (m := fm_model a)
                  (VEmp _ _)
                  (compile_simplified_entailment e
                    (compile_buf buf1)
                    (compile_buf buf2)
                    (compile_store store1)
                    (compile_store store2)).
  Proof.
  Admitted.

End CompileConfRelSimplified.
