Require Import Coq.Classes.EquivDec.
Require Import Coq.Relations.Relations.
Require Import Coq.Program.Program.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Import Lia.

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
  Variable (H: nat -> Type).
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Definition state_pair : Type :=
    state_template a * state_template a.
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

  Definition advance (steps: nat) (t1: state_template a) (s: P4A.state_ref S) :=
    match s with
    | inl s =>
      let st := P4A.t_states a s in
      if Compare_dec.le_gt_dec (size (P4A.interp a) s) (t1.(st_buf_len) + steps)
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
    | Datatypes.S fuel => reachable_step (reachable_states' fuel r)
    end.

  Lemma nodup_incl' {X: Type} {Heq: EqDec X eq}:
    forall (l1 l2: list X),
      List.incl l1 l2 <-> List.incl (List.nodup Heq l1) l2.
  Proof.
    split; intros.
    - induction l1; try easy.
      simpl.
      destruct (List.in_dec Heq a0 l1).
      + apply IHl1.
        apply List.incl_cons_inv in H0.
        intuition.
      + apply List.incl_cons_inv in H0.
        apply List.incl_cons; try easy.
        intuition.
    - induction l1; try easy.
      apply List.incl_cons.
      + apply H0.
        simpl.
        destruct (List.in_dec Heq a0 l1).
        * now apply List.nodup_In.
        * now left.
      + apply IHl1.
        simpl in H0.
        destruct (List.in_dec Heq a0 l1).
        * assumption.
        * apply List.incl_cons_inv in H0.
          intuition.
  Qed.

  Lemma reachable_step_mono:
    forall r1 r2,
      List.incl r1 r2 ->
      List.incl (reachable_step r1) (reachable_step r2).
  Proof.
    intros.
    unfold reachable_step.
    rewrite List.nodup_incl.
    rewrite <- nodup_incl'.
    repeat rewrite <- List.flat_map_concat_map.
    apply List.incl_app.
    - apply List.incl_appl.
      intros ? ?.
      rewrite List.in_flat_map_Exists in *.
      now apply List.incl_Exists with (l1 := r1).
    - now apply List.incl_appr.
  Qed.

  Lemma reachable_states_mono:
    forall fuel r1 r2,
      List.incl r1 r2 ->
      List.incl (reachable_states' fuel r1)
                (reachable_states' fuel r2).
  Proof.
    induction fuel; intros.
    - simpl in *.
      now apply H0.
    - simpl in *.
      apply reachable_step_mono.
      unfold reachable_step in *.
      now apply IHfuel.
  Qed.

  Lemma reachable_states_plus:
    forall f1 f2 r,
      reachable_states' (f1 + f2) r =
      reachable_states' f1 (reachable_states' f2 r).
  Proof.
    induction f1; intros.
    - rewrite plus_O_n.
      reflexivity.
    - replace (Datatypes.S f1 + f2) with (Datatypes.S (f1 + f2)) by lia.
      simpl.
      now rewrite IHf1.
  Qed.

  Lemma reachable_states_expansive:
    forall fuel r,
      List.incl r (reachable_states' fuel r).
  Proof.
    induction fuel; intros.
    - easy.
    - simpl.
      unfold reachable_step.
      rewrite List.nodup_incl.
      apply List.incl_appr.
      apply IHfuel.
  Qed.

  Lemma reachable_states_mono_fuel:
    forall f1 f2 r,
      f1 <= f2 ->
      List.incl (reachable_states' f1 r) (reachable_states' f2 r).
  Proof.
    intros.
    replace f2 with (f1 + (f2-f1)) by lia.
    rewrite reachable_states_plus.
    apply reachable_states_mono.
    apply reachable_states_expansive.
  Qed.

  Definition chain (l: list state_pair) :=
    forall l1 l2 p1 p2,
      l = l1 ++ [p1; p2] ++ l2 ->
      List.In p2 (reachable_pair_step p1).

  Lemma chain_split_left:
    forall l1 l2,
      chain (l1 ++ l2) ->
      chain l1.
  Proof.
    unfold chain.
    intros.
    apply (H0 l0 (l3 ++ l2)).
    repeat rewrite List.app_assoc.
    f_equal.
    now repeat rewrite <- List.app_assoc.
  Qed.

  Lemma chain_trivial:
    forall p, chain [p].
  Proof.
    unfold chain; intros.
    apply (f_equal (@List.length state_pair)) in H0.
    repeat rewrite List.app_length in H0.
    simpl in H0.
    lia.
  Qed.

  Lemma chain_cons (p p': state_pair) (l: list state_pair):
    chain (l ++ [p]) ->
    List.In p' (reachable_pair_step p) ->
    chain (l ++ [p; p']).
  Proof.
    unfold chain in *; intros.
    destruct l2.
    - simpl in *.
      apply (f_equal (@List.rev state_pair)) in H2.
      repeat rewrite List.rev_app_distr in H2.
      simpl in H2.
      inversion H2.
      now subst.
    - apply (f_equal (@List.removelast state_pair)) in H2.
      replace [p; p'] with ([p] ++ [p']) in H2 by easy.
      rewrite List.app_assoc in H2.
      rewrite List.removelast_last in H2.
      rewrite List.app_assoc in H2.
      rewrite List.removelast_app in H2 by easy.
      apply (H0 l1 (List.removelast (s :: l2))).
      rewrite <- List.app_assoc in H2.
      exact H2.
  Qed.

  Lemma nodup_trivial {X: Type} (x: X):
    List.NoDup [x].
  Proof.
    constructor.
    - easy.
    - constructor.
  Qed.

  Lemma nodup_split_left {X: Type} (l1 l2: list X):
    List.NoDup (l1 ++ l2) ->
    List.NoDup l1.
  Proof.
    revert l2; induction l1; intros.
    - constructor.
    - inversion_clear H0.
      constructor.
      + contradict H1.
        apply List.in_app_iff.
        now left.
      + now eapply IHl1 with (l2 := l2).
  Qed.

  Lemma reachability_sound fuel p r:
    List.In p (reachable_states' fuel r) ->
    exists lpre lpost s,
      List.In s r /\
      s :: lpost = lpre ++ [p] /\
      chain (s :: lpost) /\
      List.NoDup (s :: lpost).
  Proof.
    revert p r; induction fuel; intros.
    - simpl in H0.
      exists nil, nil, p.
      simpl; repeat split; auto.
      + apply chain_trivial.
      + apply nodup_trivial.
    - simpl in H0.
      unfold reachable_step in H0.
      rewrite List.nodup_In, List.in_app_iff in H0.
      destruct H0; [|now apply IHfuel].
      rewrite <- List.flat_map_concat_map,
              List.in_flat_map_Exists,
              List.Exists_exists in H0.
      destruct H0 as [p' [? ?]].
      apply IHfuel in H0.
      destruct H0 as [lpre' [lpost' [s [? [? [? ?]]]]]].
      destruct (List.in_dec state_pair_eq_dec p ([s] ++ lpost')).
      + apply List.in_split in i.
        destruct i as [l1 [l2 ?]].
        exists l1.
        destruct l1.
        * exists nil, s.
          simpl in *.
          repeat split; auto.
          -- now inversion_clear H5.
          -- apply chain_trivial.
          -- apply nodup_trivial.
        * simpl in *.
          exists (l1 ++ [p]), s.
          repeat split; auto.
          -- now inversion_clear H5.
          -- rewrite H5 in H3.
             apply chain_split_left with (l2 := l2).
             inversion_clear H5.
             simpl.
             now rewrite <- List.app_assoc.
          -- rewrite H5 in H4.
             inversion_clear H5.
             eapply nodup_split_left with (l4 := l2).
             now rewrite <- List.app_comm_cons, <- List.app_assoc.
      + exists (lpre' ++ [p']), (lpost' ++ [p]), s.
        repeat split; auto.
        * rewrite List.app_comm_cons.
          now f_equal.
        * rewrite List.app_comm_cons, H2.
          rewrite <- List.app_assoc.
          apply chain_cons; auto.
          now rewrite <- H2.
        * rewrite List.app_comm_cons.
          apply NoDup_app; auto.
          -- apply nodup_trivial.
          -- intros.
             contradict n.
             inversion_clear n; try contradiction.
             now subst.
          -- intros.
             inversion_clear H5; try contradiction.
             now subst.
  Qed.

  Lemma reachability_complete':
    forall lpost lpre s p r,
      List.In s r ->
      s :: lpost = lpre ++ [p] ->
      chain (s :: lpost) ->
      List.In p (reachable_states' (length lpost) r).
  Proof.
    induction lpost using List.rev_ind; intros.
    - simpl.
      destruct lpre.
      + simpl in H1.
        inversion H1.
        now subst.
      + apply (f_equal (@List.length state_pair)) in H1.
        rewrite List.app_length in H1.
        simpl in H1.
        lia.
    - simpl.
      induction lpre using List.rev_ind.
      + simpl in H1.
        inversion H1.
        apply (f_equal (@List.rev state_pair)) in H5.
        simpl in H5.
        rewrite List.rev_unit in H5.
        discriminate.
      + rewrite List.app_length; simpl.
        replace (length lpost + 1) with (Datatypes.S (length lpost)) by lia; simpl.
        unfold reachable_step.
        rewrite List.nodup_In.
        rewrite List.in_app_iff.
        left.
        rewrite <- List.flat_map_concat_map.
        rewrite List.in_flat_map_Exists.
        rewrite List.Exists_exists.
        simpl in H1.
        exists x0.
        split.
        * eapply IHlpost with (s := s); auto.
          -- rewrite <- List.removelast_last with (a := x) at 1.
             rewrite <- List.removelast_last with (a := p).
             rewrite <- List.app_comm_cons.
             rewrite H1.
             reflexivity.
          -- unfold chain in *; intros.
             apply H2 with (l1 := l1) (l2 := l2 ++ [x]).
             rewrite List.app_comm_cons, H3.
             now repeat rewrite <- List.app_assoc.
        * rewrite H1 in H2.
          rewrite <- List.app_assoc in H2.
          simpl in H2.
          unfold chain in H2.
          apply H2 with (l1 := lpre) (l2 := nil).
          reflexivity.
  Qed.

  Lemma reachability_complete:
    forall lpost lpre s p r n,
      List.In s r ->
      s :: lpost = lpre ++ [p] ->
      chain (s :: lpost) ->
      length lpost <= n ->
      List.In p (reachable_states' n r).
  Proof.
    intros.
    apply reachable_states_mono_fuel with (f1 := length lpost); auto.
    now apply reachability_complete' with (s := s) (lpre := lpre).
  Qed.

  Definition valid_state_templates : list (state_template a) :=
    [{| st_state := inr false; st_buf_len := 0 |};
     {| st_state := inr true; st_buf_len := 0 |}] ++
    List.flat_map (fun s =>
      List.map (fun n => {| st_state := inl s; st_buf_len := n |})
               (List.seq 0 (size (P4A.interp a) s))
      ) (List.map inl (enum S1) ++ List.map inr (enum S2)).

  Definition valid_state_template (t: state_template a) :=
    match st_state t with
    | inr _ => st_buf_len t = 0
    | inl s => st_buf_len t < size (P4A.interp a) s
    end.

  Lemma valid_state_templates_accurate:
    forall t,
      valid_state_template t ->
      List.In t valid_state_templates.
  Proof.
    unfold valid_state_template; intros.
    destruct t.
    simpl in *.
    destruct st_state.
    - right; right.
      rewrite List.in_flat_map_Exists.
      rewrite List.Exists_exists.
      exists s.
      split.
      + rewrite List.in_app_iff.
        destruct s; [left | right];
        rewrite List.in_map_iff;
        exists s;
        split; auto;
        apply elem_of_enum.
      + rewrite List.in_map_iff.
        exists st_buf_len.
        split; auto.
        apply List.in_seq.
        lia.
    - destruct b; [right; left | left].
      all: now f_equal.
  Qed.

  Lemma valid_state_templates_closed:
    forall t,
      valid_state_template t ->
      (forall t' n,
        List.In t' (advance n t (st_state t)) ->
        valid_state_template t').
  Proof.
    unfold valid_state_template; intros.
    destruct (st_state t) eqn:?.
    - simpl in H1.
      destruct (Compare_dec.le_gt_dec _ _).
      + rewrite List.in_map_iff in H1.
        destruct H1 as [? [? ?]].
        rewrite <- H1; simpl.
        destruct x; auto.
        apply a.
      + destruct H1; try contradiction.
        rewrite <- H1.
        simpl.
        rewrite Heqs.
        unfold P4A.t_states in g.
        simpl in H0.
        simpl.
        lia.
   - destruct H1.
     + now rewrite <- H1.
     + contradiction.
  Qed.

  Definition valid_state_pair (p: state_pair) :=
    valid_state_template (fst p) /\ valid_state_template (snd p).

  Definition valid_state_pairs :=
    List.list_prod valid_state_templates valid_state_templates.

  Lemma valid_state_pairs_closed:
    forall p,
      valid_state_pair p ->
      (forall p',
        List.In p' (reachable_pair_step p) ->
        valid_state_pair p').
  Proof.
    unfold valid_state_pair in *; intros.
    unfold reachable_pair_step in H1.
    unfold reachable_pair_step' in H1.
    destruct p, p'.
    unfold snd in H1.
    apply List.in_prod_iff in H1.
    destruct H1.
    simpl in H0; destruct H0.
    simpl; split.
    - eapply valid_state_templates_closed with (t := s); auto.
      exact H1.
    - eapply valid_state_templates_closed with (t := s0); auto.
      exact H2.
  Qed.

  Lemma valid_state_pairs_accurate:
    forall p,
      valid_state_pair p ->
      List.In p valid_state_pairs.
  Proof.
    intros.
    destruct p.
    unfold valid_state_pairs.
    apply List.in_prod_iff.
    unfold valid_state_pair in H0.
    simpl in H0.
    split; now apply valid_state_templates_accurate.
  Qed.

  Lemma chain_preserve_valid:
    forall l p,
      valid_state_pair p ->
      chain (p :: l) ->
      forall p',
        List.In p' l ->
        valid_state_pair p'.
  Proof.
    induction l; intros.
    - contradiction.
    - assert (valid_state_pair a0).
      + apply (valid_state_pairs_closed H0).
        now apply H1 with (l1 := nil) (l2 := l).
      + destruct H2.
        * subst; auto.
        * apply IHl with (p := a0); auto.
          unfold chain in *.
          intros.
          eapply H1 with (l1 := p :: l1) (l2 := l2).
          simpl.
          now f_equal.
  Qed.

  Lemma reachable_states_bound:
    forall fuel r,
      (forall p, List.In p r -> valid_state_pair p) ->
      List.incl (reachable_states' fuel r)
                (reachable_states' (length valid_state_pairs) r).
  Proof.
    intros.
    intros ? ?.
    apply reachability_sound in H1.
    destruct H1 as [lpre [lpost [s [? [? [? ?]]]]]].
    eapply reachability_complete with (s := s).
    - auto.
    - exact H2.
    - exact H3.
    - apply List.NoDup_incl_length; [now inversion H4 |].
      clear H2.
      induction lpost using List.rev_ind; intros; try easy.
      apply List.incl_app.
      + apply IHlpost.
        * now apply chain_split_left with (l2 := [x]).
        * now eapply nodup_split_left with (l2 := [x]).
      + unfold List.incl; intros.
        destruct H2; [subst | easy].
        apply valid_state_pairs_accurate.
        apply chain_preserve_valid with (p := s) (l := lpost ++ [a1]); auto.
        rewrite List.in_app_iff; right.
        apply List.in_eq.
  Qed.

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
