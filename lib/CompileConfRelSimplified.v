From Equations Require Import Equations.
Require Import Coq.Program.Equality.

Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FirstOrderConfRelSimplified.
Require Import Leapfrog.Ntuple.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Import HListNotations.

Set Universe Polymorphism.

Section CompileConfRelSimplified.
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

  Fixpoint compile_bctx (b: bctx): ctx (sig Hdr_sz) :=
    match b with
    | BCEmp => SLNil _
    | BCSnoc b size => Snoc _ (compile_bctx b) (Bits size)
    end.

  Definition be_sort {c} b1 b2 (e: bit_expr Hdr c) : sorts :=
    Bits (be_size Hdr_sz b1 b2 e).

  Equations compile_var {c: bctx} (x: bvar c) : var (sig Hdr_sz) (compile_bctx c) (Bits (check_bvar x)) :=
    { compile_var (BVarTop c size) :=
        VHere _ (compile_bctx c) (Bits (check_bvar (BVarTop c size)));
      compile_var (BVarRest y) :=
        VThere _ (compile_bctx _) _ (Bits (check_bvar y)) (compile_var y) }.

  Equations compile_bval (c: bctx) (v: bval c) : valu _ (fm_model a) (compile_bctx c) by struct c := {
    compile_bval BCEmp _ := VEmp _ _;
    compile_bval (BCSnoc c' n) (v', x) := VSnoc _ (fm_model a) (Bits n) _ (compile_bval c' v') x;
  }.

  Arguments compile_bval {_} _.

  Equations decompile_val (c: bctx) (v: valu _ (fm_model a) (compile_bctx c)) : bval c by struct c := {
      decompile_val BCEmp _ := tt;
      decompile_val (BCSnoc c' n) (VSnoc _ _ _ _ v' x) := (decompile_val c' v', x);
  }.
  Arguments decompile_val {_} _.

  Lemma bval_roundtrip:
    forall {c: bctx} (valu: _ (fm_model a) (compile_bctx c)),
      compile_bval (decompile_val valu) = valu.
  Proof.
    intros.
    induction c.
    - simpl.
      dependent destruction valu.
      trivial.
    - dependent destruction valu.
      autorewrite with decompile_val.
      autorewrite with compile_bval.
      erewrite IHc.
      trivial.
  Qed.

  Definition outer_ctx b1 b2 : ctx (sig Hdr_sz) :=
    Snoc _ (
      Snoc _ (
        Snoc _ (
          Snoc _ (SLNil _) Store
        ) Store
      ) (Bits b2)
    ) (Bits b1).

  Definition var_buf1 b1 b2 : var (sig Hdr_sz) (outer_ctx b1 b2) (Bits b1) :=
    VHere (sig Hdr_sz) _ _.

  Definition var_buf2 b1 b2 : var (sig Hdr_sz) (outer_ctx b1 b2) (Bits b2) :=
    VThere (sig Hdr_sz) _ _ _ (VHere (sig Hdr_sz) _ _).

  Definition var_store1 b1 b2 : var (sig Hdr_sz) (outer_ctx b1 b2) Store :=
    VThere (sig Hdr_sz) _ _ _ (VThere (sig Hdr_sz) _ _ _ (VHere (sig Hdr_sz) _ _)).

  Definition var_store2 b1 b2 : var (sig Hdr_sz) (outer_ctx b1 b2) Store :=
    VThere (sig Hdr_sz) _ _ _ (VThere (sig Hdr_sz) _ _ _ (
    VThere (sig Hdr_sz) _ _ _ (VHere (sig Hdr_sz) _ _))).

  Definition outer_valu {b1 b2} buf1 buf2 store1 store2 :=
    VSnoc _ (fm_model a) (Bits b1) _ (
      VSnoc _ (fm_model a) (Bits b2) _ (
        VSnoc _ (fm_model a) Store _ (
          VSnoc _ (fm_model a) Store _ (VEmp _ _) store2)
        store1)
      buf2)
    buf1.

  Equations compile_bit_expr
            {c: bctx}
            (b1 b2: nat)
            (e: bit_expr Hdr c)
    : tm (sig Hdr_sz) (app_ctx (outer_ctx b1 b2) (compile_bctx c)) (be_sort b1 b2 e) :=
    { compile_bit_expr b1 b2 (BELit _ _ l) :=
        TFun (sig Hdr_sz) (BitsLit _ (List.length l) (Ntuple.l2t l)) hnil;
      compile_bit_expr b1 b2 (BEBuf _ _ Left) :=
        TVar (weaken_var _ (var_buf1 b1 b2));
      compile_bit_expr b1 b2 (BEBuf _ _ Right) :=
        TVar (weaken_var _ (var_buf2 b1 b2));
      compile_bit_expr b1 b2 (BEHdr _ Left (P4A.HRVar h)) :=
        TFun (sig Hdr_sz) (Lookup _ h)
             (TVar (weaken_var _ (var_store1 b1 b2)) ::: hnil);
      compile_bit_expr b1 b2 (BEHdr _ Right (P4A.HRVar h)) :=
        TFun (sig Hdr_sz) (Lookup _ h)
             (TVar (weaken_var _ (var_store2 b1 b2)) ::: hnil);
      compile_bit_expr b1 b2 (BEVar _ b) :=
        TVar (reindex_var (compile_var b));
      compile_bit_expr b1 b2 (BESlice e hi lo) :=
        TFun (sig Hdr_sz) (Slice _ _ hi lo)
             (compile_bit_expr b1 b2 e ::: hnil);
      compile_bit_expr b1 b2 (BEConcat e1 e2) :=
      simplify_concat_zero (
        TFun (sig Hdr_sz) (Concat _ _ _)
             (compile_bit_expr b1 b2 e1 :::
              compile_bit_expr b1 b2 e2 ::: hnil)) }.

  Equations compile_store_rel
            {c: bctx}
            (b1 b2: nat)
            (r: store_rel Hdr c)
            : fm (sig Hdr_sz) (app_ctx (outer_ctx b1 b2) (compile_bctx c)) :=
    { compile_store_rel b1 b2 BRTrue := FTrue;
      compile_store_rel b1 b2 BRFalse := FFalse;
      compile_store_rel b1 b2 (BREq e1 e2) :=
        match eq_dec (be_size Hdr_sz b1 b2 e1) (be_size Hdr_sz b1 b2 e2) with
        | left Heq =>
          FEq (eq_rect _ (fun n => tm (sig Hdr_sz) _ (Bits n))
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
    (r: simplified_conf_rel Hdr)
    : fm (sig Hdr_sz) (outer_ctx b1 b2)
  :=
    let sr: fm (sig Hdr_sz) _ :=
        compile_store_rel b1 b2 (projT2 r)
    in
    quantify _ sr.

  Definition compile_simplified_crel
    (b1 b2: nat)
    (R: simplified_crel Hdr)
    : fm (sig Hdr_sz) (outer_ctx b1 b2) :=
    List.fold_right (fun r f =>
      FAnd _ (compile_simplified_conf_rel b1 b2 r) f
    ) FTrue R.

  (* Compilation from simplified entailments to FOL(Conf). *)
  Definition compile_simplified_entailment
    (se: simplified_entailment a)
    : fm (sig Hdr_sz) (SLNil _) :=
    quantify_all _
      (FImpl (compile_simplified_crel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_prems))
             (compile_simplified_conf_rel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_concl))).

  (* Compilation from simplified co-entailments to FOL(Conf). *)
  Definition compile_simplified_entailment'
    (se: simplified_entailment a)
    : fm (sig Hdr_sz) (SLNil _) :=

    quantify_all _
      (FImpl (compile_simplified_conf_rel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_concl))
             (compile_simplified_crel
               se.(se_st).(cs_st1).(st_buf_len)
               se.(se_st).(cs_st2).(st_buf_len)
               se.(se_prems))).

  Lemma compile_bvar_correct:
    forall c bval (b: bvar c),
      interp_bvar bval b =
      find (sig Hdr_sz) (fm_model a) (compile_var b) (compile_bval bval).
  Proof.
    induction c; intros.
    - dependent destruction b.
    - destruct bval.
      dependent destruction b;
      autorewrite with interp_bvar; auto.
      now rewrite IHc.
  Qed.

  Lemma compile_bit_expr_correct:
    forall c (e: bit_expr Hdr c) bval b1 b2 buf1 buf2 store1 store2,
      interp_bit_expr e bval buf1 buf2 store1 store2 =
      let valu := outer_valu buf1 buf2 store1 store2 in
      interp_tm (m := fm_model a) (app_valu _ valu (compile_bval bval))
                (compile_bit_expr b1 b2 e).
  Proof.
    intros; simpl.
    induction e; try destruct a0; try destruct h;
    autorewrite with interp_bit_expr;
    autorewrite with compile_bit_expr;
    autorewrite with interp_tm; auto.
    - now rewrite find_app_left.
    - now rewrite find_app_left.
    - simpl; autorewrite with mod_fns.
      now rewrite find_app_left.
    - simpl; autorewrite with mod_fns.
      now rewrite find_app_left.
    - rewrite find_app_right.
      apply compile_bvar_correct.
    - now rewrite IHe.
    - rewrite IHe1, IHe2.
      now erewrite <- simplify_concat_zero_corr by typeclasses eauto.
  Qed.

  Lemma compile_store_rel_correct:
    forall c (r: store_rel Hdr c) bval b1 b2 buf1 buf2 store1 store2,
      interp_store_rel r bval buf1 buf2 store1 store2 <->
      let valu := outer_valu buf1 buf2 store1 store2 in
      interp_fm (m := fm_model a) (app_valu _ valu (compile_bval bval))
                (compile_store_rel b1 b2 r).
  Proof.
    intros; simpl.
    induction r;
    autorewrite with interp_store_rel;
    autorewrite with compile_store_rel;
    try destruct (eq_dec _ _);
    autorewrite with interp_fm;
    try tauto.
    rewrite <- interp_tm_rect.
    repeat erewrite <- simplify_concat_zero_corr by typeclasses eauto.
    repeat rewrite compile_bit_expr_correct; simpl.
    intuition.
  Qed.

  Lemma compile_simplified_conf_rel_correct:
    forall r b1 b2 buf1 buf2 store1 store2,
      interp_simplified_conf_rel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (outer_valu buf1 buf2 store1 store2)
                (compile_simplified_conf_rel b1 b2 r).
  Proof.
    intros; destruct r.
    unfold interp_simplified_conf_rel, compile_simplified_conf_rel.
    rewrite quantify_correct; simpl.
    setoid_rewrite compile_store_rel_correct; simpl.
    split; intros; auto.
    now rewrite <- bval_roundtrip with (valu := valu).
  Qed.

  Lemma compile_simplified_crel_correct:
    forall r b1 b2 buf1 buf2 store1 store2,
      interp_simplified_crel r buf1 buf2 store1 store2 <->
      interp_fm (m := fm_model a) (outer_valu buf1 buf2 store1 store2)
                (compile_simplified_crel b1 b2 r).
  Proof.
    intros.
    induction r;
    autorewrite with interp_simplified_crel; simpl;
    autorewrite with interp_fm.
    - intuition.
    - now rewrite compile_simplified_conf_rel_correct, IHr.
  Qed.

  Transparent interp_fm.

  (* Correctness of compilation from simplified entailments to FOL(Conf). *)
  Lemma compile_simplified_entailment_correct:
      forall i e,
        interp_simplified_entailment i e <->
        (state_template_sane e.(se_st).(cs_st1) ->
         state_template_sane e.(se_st).(cs_st2) ->
         i e.(se_st).(cs_st1) e.(se_st).(cs_st2) ->
         interp_fm (m := fm_model a) (VEmp _ _)
                   (compile_simplified_entailment e)
        ).
  Proof.
    intros.
    destruct e.
    unfold interp_simplified_entailment; simpl.
    unfold compile_simplified_entailment; simpl.
    rewrite quantify_all_correct; simpl.
    setoid_rewrite compile_simplified_crel_correct.
    setoid_rewrite compile_simplified_conf_rel_correct.
    intuition.
    unfold outer_ctx in valu.
    repeat dependent destruction valu.
    simpl in *.
    eauto.
  Qed.

  (* Correctness of compilation from simplified co-entailments to FOL(Conf). *)
  Lemma compile_simplified_entailment_correct':
      forall i e,
        interp_simplified_entailment' i e <->
        (state_template_sane e.(se_st).(cs_st1) ->
         state_template_sane e.(se_st).(cs_st2) ->
         i e.(se_st).(cs_st1) e.(se_st).(cs_st2) ->
         interp_fm (m := fm_model a) (VEmp _ _)
                   (compile_simplified_entailment' e)).
  Proof.
    intros; destruct e; simpl.
    unfold interp_simplified_entailment'; simpl.
    unfold compile_simplified_entailment'; simpl.
    rewrite quantify_all_correct; simpl.
    setoid_rewrite compile_simplified_conf_rel_correct.
    setoid_rewrite compile_simplified_crel_correct.
    intuition.
    unfold outer_ctx in valu.
    repeat dependent destruction valu.
    simpl in *.
    eauto.
  Qed.

  Opaque interp_fm.

End CompileConfRelSimplified.
