From Equations Require Import Equations.

Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FirstOrderConfRel.
Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Import HListNotations.

Section CompileConfRel.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.
  Variable (sz: H -> nat).

  Variable (a: P4A.t S sz).

  Notation conf := (configuration (P4A.interp a)).

  Fixpoint compile_bctx (b: bctx): ctx (sig a) :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (compile_bctx b) (Bits size)
    end.

  Definition be_sort {c} {b1 b2: nat} (e: bit_expr H c) : sorts :=
    Bits (be_size sz b1 b2 e).

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
            (b1 b2: nat)
            (q: tm (sig a) (compile_bctx c) (ConfigPair b1 b2))
            (e: bit_expr H c)
    : tm (sig a) (compile_bctx c) (be_sort (b1 := b1) (b2 := b2) e) :=
    { compile_bit_expr q (BELit _ _ l) :=
        TFun (sig a) (BitsLit a (List.length l) (Ntuple.l2t l)) hnil;
      compile_bit_expr q (BEBuf _ _ Left) :=
        TFun (sig a) (Buf1 _ b1 b2) (q ::: hnil);
      compile_bit_expr q (BEBuf _ _ Right) :=
        TFun (sig a) (Buf2 _ b1 b2) (q ::: hnil);
      compile_bit_expr q (@BEHdr H _ Left (P4A.HRVar h)) :=
        let store := TFun (sig a) (Store1 a b1 b2) (q ::: hnil) in
        TFun (sig a) (Lookup a h) (store ::: hnil);
      compile_bit_expr q (BEHdr _ Right (P4A.HRVar h)) :=
        let store := TFun (sig a) (Store2 a b1 b2) (q ::: hnil) in
        TFun (sig a) (Lookup a h) (store ::: hnil);
      compile_bit_expr q (BEVar _ b) :=
        TVar (compile_var b);
      compile_bit_expr q (BESlice e hi lo) :=
        TFun (sig a) (Slice a _ hi lo) (compile_bit_expr q e ::: hnil);
      compile_bit_expr q (BEConcat e1 e2) :=
        TFun (sig a) (Concat _ _ _) (compile_bit_expr q e1 ::: compile_bit_expr q e2 ::: hnil) }.

  Equations compile_store_rel
            {c: bctx}
            {b1 b2: nat}
            (q: tm (sig a) (compile_bctx c) (ConfigPair b1 b2))
            (r: store_rel H c)
            : fm (sig a) (compile_bctx c) :=
    { compile_store_rel q BRTrue := FTrue;
      compile_store_rel q BRFalse := FFalse;
      compile_store_rel q (BREq e1 e2) :=
        match eq_dec (be_size sz b1 b2 e1) (be_size sz b1 b2 e2) with
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
    {n m: nat}
    (r: conf_rel a)
    (q: tm (sig a) (CEmp _) (ConfigPair n m))
    : fm (sig a) (CEmp _)
  :=
    let s1 := r.(cr_st).(cs_st1).(st_state) in
    let s2 := r.(cr_st).(cs_st2).(st_state) in
    let s1eq :=
        FAnd _ (FEq (TFun (sig a) (State1 a n m) (q ::: hnil))
                    (TFun (sig a) (StateLit _ s1) hnil))
               (FEq (TFun (sig a) (NatLit _ n) hnil)
                    (TFun (sig a) (NatLit _ r.(cr_st).(cs_st1).(st_buf_len)) hnil))
    in
    let s2eq :=
        FAnd _ (FEq (TFun (sig a) (State2 a n m) (q ::: hnil))
                    (TFun (sig a) (StateLit _ s2) hnil))
               (FEq (TFun (sig a) (NatLit _ m) hnil)
                    (TFun (sig a) (NatLit _ r.(cr_st).(cs_st2).(st_buf_len)) hnil))
    in
    let sr: fm (sig a) _ :=
        (compile_store_rel (reindex_tm q) r.(cr_rel))
    in
    FImpl s1eq (FImpl s2eq (quantify_all _ sr)).

  Definition compile_crel
    {n m: nat}
    (R: crel a)
    (i: fm (sig a) (CEmp _))
    (q: tm (sig a) (CEmp _) (ConfigPair n m))
    : fm (sig a) (CEmp _) :=
    List.fold_right (fun r f => FAnd _ (compile_conf_rel r q) f) i R.

  Definition compile_entailment
    {n m: nat}
    (e: entailment a)
    (i: fm (sig a) (CEmp _))
    (q: tm (sig a) (CEmp _) (ConfigPair n m))
    : fm (sig a) (CEmp _) :=
    (FImpl (compile_crel e.(e_prem) i q)
           (compile_conf_rel e.(e_concl) q)).

  Definition compile_config
    {c': ctx (sig a)}
    (q1 q2: conf)
    : tm (sig a) c' (ConfigPair q1.(conf_buf_len)
                                q2.(conf_buf_len)) :=
    let q1' : conf' a q1.(conf_buf_len) :=
        exist (fun c => c.(conf_buf_len) = q1.(conf_buf_len)) q1 eq_refl in
    let q2' : conf' a q2.(conf_buf_len) :=
        exist (fun c => c.(conf_buf_len) = q2.(conf_buf_len)) q2 eq_refl in
    TFun (sig a) (ConfPairLit (q1', q2')) hnil.

  Lemma compile_store_rel_correct:
    forall c (r: store_rel H c) valu q1 q2,
      interp_store_rel r valu q1.(conf_buf) q2.(conf_buf)
                       q1.(conf_store) q2.(conf_store) <->
      interp_fm (m := fm_model a) (compile_bval valu)
                (compile_store_rel (compile_config q1 q2) r).
  Proof.
  Admitted.

  Lemma compile_conf_rel_correct:
    forall r q1 q2,
      interp_conf_rel a r q1 q2 <->
      interp_fm (m := fm_model a) (VEmp _ _) (compile_conf_rel r (compile_config q1 q2)).
  Proof.
    destruct r.
    unfold interp_conf_rel, compile_conf_rel.
    unfold interp_conf_state, interp_state_template.
    simpl.
    intros q1 q2.
    repeat (progress cbn || autorewrite with interp_fm mod_fns weaken_tm).
    autorewrite with interp_fm.
    setoid_rewrite quantify_all_correct; eauto.
    setoid_rewrite compile_store_rel_correct.
    fold (compile_bctx cr_ctx).
    intuition.
    specialize (H0 (eq_sym H3) (eq_sym H4) (conj (eq_sym H1) (eq_sym H5))).
    specialize (H0 (decompile_val valu)).
    rewrite bval_roundtrip in H0.
    auto.
  Qed.

  Lemma compile_crel_correct:
    forall R i ifm q1 q2,
      (forall q1 q2, i q1 q2 <-> interp_fm (VEmp _ (fm_model a)) ifm) ->
      interp_crel a i R q1 q2 <->
      interp_fm (m := fm_model a) (VEmp _ _) (compile_crel R ifm (compile_config q1 q2)).
  Proof.
    unfold interp_crel, compile_crel.
    induction R.
    - simpl; intros.
      apply H0.
    - intros.
      cbn in *; autorewrite with interp_fm in *.
      rewrite compile_conf_rel_correct.
      unfold Relations.interp_rels in IHR.
      rewrite IHR by auto.
      reflexivity.
  Qed.

  Lemma compile_entailment_correct:
    forall e i ifm,
      (forall q1 q2, i q1 q2 <-> interp_fm (VEmp _ (fm_model a)) ifm) ->
      interp_entailment a i e <->
      forall q1 q2, interp_fm (m := fm_model a)
                (VEmp _ _)
                (compile_entailment e ifm (compile_config q1 q2)).
  Proof.
    intros.
    unfold interp_entailment.
    unfold compile_entailment.
    setoid_rewrite compile_conf_rel_correct.
    pose proof compile_crel_correct.
    specialize (H1 (e_prem e) i ifm).
    split; intros.
    - autorewrite with interp_fm.
      intros.
      apply H2.
      now rewrite H1 by auto.
    - specialize (H2 q1 q2).
      autorewrite with interp_fm in H2.
      apply H2.
      now apply compile_crel_correct with (i := i).
  Qed.

End CompileConfRel.
