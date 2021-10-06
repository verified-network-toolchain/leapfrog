From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrderConfRelSimplified.
Require Import Poulet4.P4automata.Ntuple.

Import FirstOrder.
Import HListNotations.

Section CompileConfRelSimplified.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Fixpoint compile_bctx (b: bctx): ctx (sig H) :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (compile_bctx b) (Bits size)
    end.

  Definition be_sort {c} b1 b2 (e: bit_expr H c) : sorts :=
    Bits (be_size b1 b2 e).

  Equations compile_var {c: bctx} (x: bvar c) : var (sig H) (compile_bctx c) (Bits (check_bvar x)) :=
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

  Definition outer_ctx b1 b2 :=
    CSnoc (sig H) (
      CSnoc (sig H) (
        CSnoc (sig H) (
          CSnoc (sig H) (CEmp (sig H)) Store
        ) Store
      ) (Bits b2)
    ) (Bits b1).

  Definition var_buf1 b1 b2 : var (sig H) (outer_ctx b1 b2) (Bits b1) :=
    VHere (sig H) _ _.

  Definition var_buf2 b1 b2 : var (sig H) (outer_ctx b1 b2) (Bits b2) :=
    VThere (sig H) _ _ _ (VHere (sig H) _ _).

  Definition var_store1 b1 b2 : var (sig H) (outer_ctx b1 b2) Store :=
    VThere (sig H) _ _ _ (VThere (sig H) _ _ _ (VHere (sig H) _ _)).

  Definition var_store2 b1 b2 : var (sig H) (outer_ctx b1 b2) Store :=
    VThere (sig H) _ _ _ (VThere (sig H) _ _ _ (
    VThere (sig H) _ _ _ (VHere (sig H) _ _))).

  Definition outer_valu {b1 b2} buf1 buf2 store1 store2 :=
    VSnoc _ (fm_model a) (Bits b1) _ buf1 (
    VSnoc _ (fm_model a) (Bits b2) _ buf2 (
    VSnoc _ (fm_model a) Store _ store1 (
    VSnoc _ (fm_model a) Store _ store2 (
    VEmp _ _)))).

  Equations compile_bit_expr
            {c: bctx}
            (b1 b2: nat)
            (e: bit_expr H c)
    : tm (sig H) (app_ctx (outer_ctx b1 b2) (compile_bctx c)) (be_sort b1 b2 e) :=
    { compile_bit_expr b1 b2 (BELit _ _ l) :=
        TFun (sig H) (BitsLit _ (List.length l) (Ntuple.l2t l)) hnil;
      compile_bit_expr b1 b2 (BEBuf _ _ Left) :=
        TVar (weaken_var _ (var_buf1 b1 b2));
      compile_bit_expr b1 b2 (BEBuf _ _ Right) :=
        TVar (weaken_var _ (var_buf2 b1 b2));
      compile_bit_expr b1 b2 (@BEHdr H _ Left (P4A.HRVar h)) :=
        TFun (sig H) (Lookup _ _ (projT2 h))
             (TVar (weaken_var _ (var_store1 b1 b2)) ::: hnil);
      compile_bit_expr b1 b2 (BEHdr _ Right (P4A.HRVar h)) :=
        TFun (sig H) (Lookup _ _ (projT2 h))
             (TVar (weaken_var _ (var_store1 b1 b2)) ::: hnil);
      compile_bit_expr b1 b2 (BEVar _ b) :=
        TVar (reindex_var (compile_var b));
      compile_bit_expr b1 b2 (BESlice e hi lo) :=
        TFun (sig H) (Slice _ _ hi lo)
             (compile_bit_expr b1 b2 e ::: hnil);
      compile_bit_expr b1 b2 (BEConcat e1 e2) :=
      simplify_concat_zero (
        TFun (sig H) (Concat _ _ _)
             (compile_bit_expr b1 b2 e1 :::
              compile_bit_expr b1 b2 e2 ::: hnil)) }.

  Equations compile_store_rel
            {c: bctx}
            (b1 b2: nat)
            (r: store_rel H c)
            : fm (sig H) (app_ctx (outer_ctx b1 b2) (compile_bctx c)) :=
    { compile_store_rel b1 b2 BRTrue := FTrue;
      compile_store_rel b1 b2 BRFalse := FFalse;
      compile_store_rel b1 b2 (BREq e1 e2) :=
        match eq_dec (be_size b1 b2 e1) (be_size b1 b2 e2) with
        | left Heq =>
          FEq (eq_rect _ (fun n => tm (sig H) _ (Bits n))
                       (simplify_concat_zero (compile_bit_expr b1 b2 e1)) _ Heq)
              (simplify_concat_zero (compile_bit_expr b1 b2 e2))
        | right _ => FFalse
        end;
      compile_store_rel b1 b2 (BRAnd r1 r2) :=
        FAnd _ (compile_store_rel b1 b2 r1)
               (compile_store_rel b1 b2 r2);
      compile_store_rel b1 b2 (BROr r1 r2) :=
        FOr _ (compile_store_rel b1 b2 r1)
              (compile_store_rel b1 b2 r2);
      compile_store_rel b1 b2 (BRImpl r1 r2) :=
        FImpl (compile_store_rel b1 b2 r1)
              (compile_store_rel b1 b2 r2)
    }.

  Definition compile_simplified_conf_rel
    (b1 b2: nat)
    (r: simplified_conf_rel H)
    : fm (sig H) (outer_ctx b1 b2)
  :=
    let sr: fm (sig H) _ :=
        compile_store_rel b1 b2 (projT2 r)
    in
    quantify _ sr.

  Definition compile_simplified_crel
    (b1 b2: nat)
    (R: simplified_crel H)
    : fm (sig H) (outer_ctx b1 b2) :=
    List.fold_right (fun r f =>
      FAnd _ (compile_simplified_conf_rel b1 b2 r) f
    ) FTrue R.

  Definition compile_simplified_entailment
    (se: simplified_entailment a)
    : fm (sig H) (CEmp _) :=
    quantify_all _
      (FImpl (compile_simplified_crel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_prems))
             (compile_simplified_conf_rel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_concl))).

  Definition compile_simplified_entailment'
    (se: simplified_entailment a)
    : fm (sig H) (CEmp _) :=
    
    quantify_all _
      (FImpl (compile_simplified_conf_rel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_concl))
             (compile_simplified_crel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_prems))).

  Lemma compile_store_rel_correct:
    forall c (r: store_rel H c) bval b1 b2 buf1 buf2 store1 store2,
      interp_store_rel r bval buf1 buf2 store1 store2 <->
      let valu := outer_valu buf1 buf2 store1 store2 in
      interp_fm (m := fm_model a) (app_valu _ valu (compile_bval bval))
                (compile_store_rel b1 b2 r).
  Proof.
  Admitted.

  Lemma compile_simplified_conf_rel_correct:
    forall r b1 b2 buf1 buf2 store1 store2,
      interp_simplified_conf_rel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (outer_valu buf1 buf2 store1 store2)
                (compile_simplified_conf_rel b1 b2 r).
  Proof.
  Admitted.

  Lemma compile_crel_correct:
    forall r b1 b2 buf1 buf2 store1 store2,
      interp_simplified_crel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (outer_valu buf1 buf2 store1 store2)
                (compile_simplified_crel b1 b2 r).
  Proof.
  Admitted.

  Lemma compile_simplified_entailment_correct:
      forall i e,
        interp_simplified_entailment i e <->
        interp_fm (m := fm_model a) (VEmp _ _) (compile_simplified_entailment e).
  Proof.
  Admitted.

  Lemma compile_simplified_entailment_correct':
      forall i e,
        interp_simplified_entailment' i e <->
        interp_fm (m := fm_model a) (VEmp _ _) (compile_simplified_entailment' e).
  Proof.
  Admitted.

End CompileConfRelSimplified.
