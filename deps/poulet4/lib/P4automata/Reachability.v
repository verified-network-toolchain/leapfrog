Require Import Coq.Classes.EquivDec.
Require Import Coq.Relations.Relations.
Require Import Coq.Program.Program.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Import List.ListNotations.

Set Implicit Arguments.
Section ReachablePairs.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Definition S: Type := S1 + S2.

  (* Header identifiers. *)
  Variable (H: Type).
  Context `{H_eq_dec: EquivDec.EqDec H eq}.
  Context `{H_finite: @Finite H _ H_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Definition state_pair : Type :=
    state_template S * state_template S.
  Global Program Instance state_pair_eq_dec: EquivDec.EqDec state_pair eq :=
    { equiv_dec x y :=
        if Sumbool.sumbool_and _ _ _ _
             (state_template_eq_dec (fst x) (fst y))
             (state_template_eq_dec (snd x) (snd y))
        then in_left
        else in_right }.
  Next Obligation.
    destruct x, y.
    simpl in *.
    congruence.
  Qed.
  Next Obligation.
    intuition.
  Qed.

  Definition state_pairs : Type :=
    list state_pair.

  Definition possible_next_states (st: P4A.state S H) : list (P4A.state_ref S) :=
    match st.(P4A.st_trans) with
    | P4A.TGoto _ s' =>
      [s']
    | P4A.TSel _ cases default =>
      default :: List.map (fun c => P4A.sc_st c) cases
    end.

  Definition reads_left (s: state_pair) : nat:=
    let '(s1, s2) := s in
    let len1 := s1.(st_buf_len) in
    let len2 := s2.(st_buf_len) in
    match s1.(st_state), s2.(st_state) with
    | inl s1, inl s2 =>
      Nat.min (P4A.size a s1 - len1)
              (P4A.size a s2 - len2)
    | inl s1, inr _ =>
      (P4A.size a s1 - len1)
    | inr _, inl s2 =>
      (P4A.size a s2 - len2)
    | inr _, inr _ => 1
    end.

  Definition advance (steps: nat) (t1: state_template S) (s: P4A.state_ref S) :=
    match s with
    | inl s =>
      let st := P4A.t_states a s in
      if t1.(st_buf_len) + steps == P4A.state_size st
      then List.map (fun r => {| st_state := r; st_buf_len := 0 |}) (possible_next_states st)
      else [{| st_state := t1.(st_state); st_buf_len := t1.(st_buf_len) + steps |}]
    | inr b => [{| st_state := inr false; st_buf_len := 0 |}]
    end.

  Definition reachable_pair_step' (r0: state_pair) : nat * state_pairs :=
    let '(t1, t2) := r0 in
    let s1 := t1.(st_state) in
    let s2 := t2.(st_state) in
    let steps := reads_left r0 in
    (steps, List.list_prod (advance steps t1 s1)
                           (advance steps t2 s2)).

  Definition reachable_pair_step (r0: state_pair) : state_pairs :=
    snd (reachable_pair_step' r0).
  
  Definition reachable_step (r: state_pairs) : state_pairs :=
    let r' := (List.concat (List.map reachable_pair_step r)) in
    List.nodup state_pair_eq_dec (r' ++ r).

  Fixpoint reachable_states' (fuel: nat) (r: state_pairs) :=
    match fuel with
    | 0 => r
    | Datatypes.S fuel => reachable_states' fuel (reachable_step r)
    end.

  Definition reachable_states n s1 s2 : state_pairs :=
    let s := ({| st_state := inl (inl s1); st_buf_len := 0 |}, 
              {| st_state := inl (inr s2); st_buf_len := 0 |}) in
    reachable_states' n [s].

  Definition reachable_pair rs (q1 q2: conf) : Prop :=
    List.Exists (fun '(t1, t2) =>
                   interp_state_template t1 q1 /\
                   interp_state_template t2 q2)
                rs.

End ReachablePairs.
