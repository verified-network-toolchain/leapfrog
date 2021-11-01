Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.Syntax.
Require Poulet4.P4automata.Reachability.
Module P4A := Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.ConfRel.
Import ListNotations.

Section WP.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := (S1 + S2)%type.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).
  Variable (reachable_states: list (state_template a * state_template a)).

  Fixpoint be_subst {c} (be: bit_expr H c) (e: bit_expr H c) (x: bit_expr H c) : bit_expr H c :=
    match be with
    | BELit _ _ l => BELit _ _ l
    | BEBuf _ _ _
    | BEHdr _ _ _
    | BEVar _ _ =>
      if bit_expr_eq_dec be x then e else be
    | BESlice be hi lo => beslice (be_subst be e x) hi lo
    | BEConcat e1 e2 => beconcat (be_subst e1 e x) (be_subst e2 e x)
    end.

  Fixpoint sr_subst {c} (sr: store_rel H c) (e: bit_expr H c) (x: bit_expr H c) : store_rel H c :=
  match sr with
  | BRTrue _ _
  | BRFalse _ _ => sr
  | BREq e1 e2 => BREq (be_subst e1 e x) (be_subst e2 e x)
  | BRAnd r1 r2 => brand (sr_subst r1 e x) (sr_subst r2 e x)
  | BROr r1 r2 => bror (sr_subst r1 e x) (sr_subst r2 e x)
  | BRImpl r1 r2 => brimpl (sr_subst r1 e x) (sr_subst r2 e x)
  end.

  Inductive lkind :=
  | Jump
  | Read.

  Definition leap_kind (pred cur: state_template a) : lkind :=
    match cur.(st_buf_len) with
    | 0 => Jump
    | _ => Read
    end.

  Fixpoint expr_to_bit_expr {c n} (s: side) (e: P4A.expr H n) : bit_expr H c :=
    match e with
    | P4A.EHdr h => BEHdr c s (P4A.HRVar (existT _ _ h))
    | P4A.ELit bs => BELit _ c (Ntuple.t2l bs)
    | P4A.ESlice e hi lo => BESlice (expr_to_bit_expr s e) hi lo
    | P4A.EConcat l r => BEConcat (expr_to_bit_expr s l) (expr_to_bit_expr s r)
    end.

  Definition val_to_bit_expr {c n} (value: P4A.v n) : bit_expr H c :=
    match value with
    | P4A.VBits _ bs => BELit _ c (Ntuple.t2l bs)
    end.

  Fixpoint wp_op' {c n} (s: side) (o: P4A.op H n) : nat * store_rel H c -> nat * store_rel H c :=
    fun '(buf_hi_idx, phi) =>
      match o with
      | P4A.OpNil _ => (buf_hi_idx, phi)
      | P4A.OpSeq o1 o2 =>
        wp_op' s o1 (wp_op' s o2 (buf_hi_idx, phi))
      | P4A.OpExtract hdr =>
        let width := projT1 hdr in
        let new_idx := buf_hi_idx - width in
        let slice := beslice (BEBuf _ _ s) (buf_hi_idx - 1) new_idx in
        (new_idx, sr_subst phi slice (BEHdr _ s (P4A.HRVar hdr)))
      | P4A.OpAsgn lhs rhs =>
        (buf_hi_idx, sr_subst phi (expr_to_bit_expr s rhs) (BEHdr _ s (P4A.HRVar (existT _ _ lhs))))
      end.

  Definition wp_op {c n} (s: side) (o: P4A.op H n) (phi: store_rel H c) : store_rel H c :=
    snd (wp_op' s o (P4A.op_size o, phi)).

  Equations pat_cond {ctx: bctx} {ty: P4A.typ} (si: side) (p: P4A.pat ty) (c: P4A.cond H ty) : store_rel H ctx :=
    { pat_cond si (P4A.PExact val) (P4A.CExpr e) :=
        BREq (expr_to_bit_expr si e) (val_to_bit_expr val);
      pat_cond _ (P4A.PAny _) _ :=
        BRTrue _ _;
      pat_cond si (P4A.PPair p1 p2) (P4A.CPair e1 e2) :=
        BRAnd (pat_cond si p1 e1) (pat_cond si p2 e2) }.

  Fixpoint cases_cond
    {ctx: bctx}
    {ty: Syntax.typ}
    (si: side)
    (cond: Syntax.cond H ty)
    (target: P4A.state_ref S)
    (cases: list (P4A.sel_case S ty))
    (default: P4A.state_ref S)
    : store_rel H ctx
  :=
    match cases with
    | nil =>
      if target == default then (BRTrue _ _) else (BRFalse _ _)
    | case :: cases =>
      if target == P4A.sc_st case
      then bror (pat_cond si case.(P4A.sc_pat) cond)
                (cases_cond si cond target cases default)
      else brand (brimpl (pat_cond si case.(P4A.sc_pat) cond) (BRFalse _ _))
                 (cases_cond si cond target cases default)
    end.

  Definition trans_cond
             {c: bctx}
             (s: side)
             (t: P4A.transition S H)
             (st': P4A.state_ref S)
    : store_rel H c :=
    match t with
    | P4A.TGoto _ r =>
      if r == st'
      then BRTrue _ _
      else BRFalse _ _
    | P4A.TSel cond cases default =>
      cases_cond s cond st' cases default
    end.

  Definition jump_cond
             {c}
             (si: side)
             (prev cur: state_template a)
    : store_rel H c :=
    match prev.(st_state) with
    | inl cand =>
      let st := a.(P4A.t_states) cand in
      trans_cond si (P4A.st_trans st) cur.(st_state)
    | inr cand =>
      match cur.(st_state) with
      | inr false => BRTrue _ _
      | _ => BRFalse _ _
      end
    end.

  Definition wp_lpred {c: bctx}
             (si: side)
             (b: bvar c)
             (prev cur: state_template a)
             (k: lkind)
             (phi: store_rel H c)
    : store_rel H c :=
    let phi' :=
    match k with
    | Read =>
      phi
    | Jump =>
      match prev.(st_state) with
      | inl s =>
        let cond := jump_cond si prev cur in
        let phi'' := sr_subst phi (BELit _ _ []) (BEBuf _ _ si) in
        wp_op si (a.(P4A.t_states) s).(P4A.st_op) (brimpl cond phi'')
      | inr s =>
        sr_subst phi (BELit _ _ []) (BEBuf _ _ si)
      end
    end in
    sr_subst phi' (beconcat (BEBuf _ _ si) (BEVar _ b)) (BEBuf _ _ si).

  Definition wp_pred_pair
             (phi: conf_rel a)
             (preds: nat * (state_template a * state_template a))
    : conf_rel a :=
    let '(size, (prev_l, prev_r)) := preds in
    let phi_rel := phi.(cr_rel) in
    let cur_l := phi.(cr_st).(cs_st1) in
    let cur_r := phi.(cr_st).(cs_st2) in
    let leap_l := leap_kind prev_l cur_l in
    let leap_r := leap_kind prev_r cur_r in
    let b := BVarTop phi.(cr_ctx) size in
    let phi_rel := weaken_store_rel size phi_rel in
    {| cr_st := {| cs_st1 := prev_l;
                   cs_st2 := prev_r |};
       cr_rel := wp_lpred Left b prev_l cur_l leap_l
                          (wp_lpred Right b prev_r cur_r leap_r phi_rel) |}.
  
  Definition reaches (cur prev: state_template a * state_template a) : list (nat * (state_template a * state_template a)) :=
    let '(n, successors) := Reachability.reachable_pair_step' prev in
    if List.In_dec (Reachability.state_pair_eq_dec (a := a))
                   cur
                   successors
    then [(n, prev)]
    else [].

  Definition wp (phi: conf_rel a) : list (conf_rel a) :=
    let cur_st_left  := phi.(cr_st).(cs_st1) in
    let cur_st_right := phi.(cr_st).(cs_st2) in
    let pred_pairs := List.flat_map (reaches (cur_st_left, cur_st_right)) reachable_states in
    List.map (wp_pred_pair phi) pred_pairs.

End WP.

Global Hint Unfold wp_lpred: wp.
Global Hint Unfold wp_pred_pair: wp.
