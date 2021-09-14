Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.FinType.
Require Poulet4.P4automata.Syntax.
Require Poulet4.P4automata.Reachability.
Module P4A := Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.ConfRel.
Require Poulet4.P4automata.WP.
Import ListNotations.

Section WeakestPreSymbolicLeap.
  Set Implicit Arguments.
  
  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Definition S: Type := S1 + S2.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (reachable_states: list (state_template S * state_template S)).
  Variable (a: P4A.t S H).

  Inductive lkind :=
  | Jump
  | Read.

  Definition leap_kind (pred cur: state_template S) : lkind :=
    match cur.(st_buf_len) with
    | 0 => Jump
    | _ => Read
    end.

  Definition jump_cond
             {c}
             (si: side)
             (prev cur: state_template S)
    : store_rel H c :=
    match prev.(st_state) with
    | inl cand => 
      let st := a.(P4A.t_states) cand in
      WP.trans_cond si (P4A.st_trans st) cur.(st_state)
    | inr cand =>
      match cur.(st_state) with
      | inr false => BRTrue _ _
      | _ => BRFalse _ _
      end
    end.

  Definition wp_lpred {c: bctx}
             (si: side)
             (b: bit_expr H c)
             (prev cur: state_template S)
             (k: lkind)
             (phi: store_rel H c)
    : store_rel H c :=
    let phi' := WP.sr_subst phi (beconcat (BEBuf _ _ si) b) (BEBuf _ _ si) in
    match k with
    | Read =>
      phi'
    | Jump =>
      WP.sr_subst
        match prev.(st_state) with
        | inl s =>
          let cond := jump_cond si prev cur in
          brimpl cond (WP.wp_op si (a.(P4A.t_states) s).(P4A.st_op) phi')
        | inr s =>
          phi'
        end
        (BELit _ _ [])
        (BEBuf _ _ si)
    end.

  Definition wp_pred_pair
             (phi: conf_rel S H)
             (preds: nat * (state_template S * state_template S))
    : list (conf_rel S H) :=
    let '(size, (prev_l, prev_r)) := preds in
    let phi_rel := phi.(cr_rel) in
    let cur_l := phi.(cr_st).(cs_st1) in
    let cur_r := phi.(cr_st).(cs_st2) in
    let leap_l := leap_kind prev_l cur_l in
    let leap_r := leap_kind prev_r cur_r in
    let b := (BEVar H (BVarTop phi.(cr_ctx) size)) in
    let phi_rel := weaken_store_rel size phi_rel in
    [{| cr_st := {| cs_st1 := prev_l;
                    cs_st2 := prev_r |};
        cr_rel := wp_lpred Left b prev_l cur_l leap_l
                           (wp_lpred Right b prev_r cur_r leap_r phi_rel) |}].

  Definition reaches (cur prev: state_template S * state_template S) :=
    let '(n, successors) := Reachability.reachable_pair_step' a prev in
    if List.In_dec (@Reachability.state_pair_eq_dec S1 _ _ S2 _ _)
                   cur 
                   successors
    then [(n, prev)]
    else [].

  Definition wp
             (phi: conf_rel S H)
    : list (conf_rel S H) :=
    let cur_st_left  := phi.(cr_st).(cs_st1) in
    let cur_st_right := phi.(cr_st).(cs_st2) in
    let pred_pairs := List.flat_map (reaches (cur_st_left, cur_st_right)) reachable_states in
    List.flat_map (wp_pred_pair phi) pred_pairs.

End WeakestPreSymbolicLeap.

Global Hint Unfold wp_lpred: wp.
Global Hint Unfold wp_pred_pair: wp.
