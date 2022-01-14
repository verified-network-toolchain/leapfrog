Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
Import List.ListNotations.

Require Import Leapfrog.FinType.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.ConfRel.

Require Import Leapfrog.Utils.FunctionalFP.

Set Implicit Arguments.
Section ReachablePairs.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  Notation St := (St1 + St2)%type.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> nat).

  Variable (a: P4A.t St Hdr_sz).

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

  Definition state_pair_eqb (l: state_pair) (r: state_pair) : bool := 
    if l == r then true else false.

  Lemma state_pair_eqb_tru : 
    forall l r, l = r <-> state_pair_eqb l r = true.
  Proof.
    unfold state_pair_eqb.
    intros.
    destruct (equiv_dec l r); [unfold "===" in e; split; auto|].
    split; intros H; exfalso; congruence.
  Qed.


  Definition state_pairs : Type :=
    list state_pair.

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

  Lemma reads_left_lower_bound (q1 q2: conf):
    1 <= reads_left
        (conf_to_state_template q1,
         conf_to_state_template q2).
  Proof.
    unfold reads_left, configuration_room_left; simpl.
    pose proof (conf_buf_sane q1).
    pose proof (conf_buf_sane q2).
    destruct (conf_state q1), (conf_state q2);
    autorewrite with size' in *; simpl in *;
    Lia.lia.
  Qed.

  Lemma reads_left_commutative (t1 t2: state_template a):
    reads_left (t1, t2) = reads_left (t2, t1).
  Proof.
    unfold reads_left.
    destruct (st_state t1), (st_state t2); Lia.lia.
  Qed.

  Lemma reads_left_upper_bound (q1 q2: conf) (s: St):
    conf_state q1 = inl s ->
    reads_left
        (conf_to_state_template q1,
         conf_to_state_template q2) <= configuration_room_left q1.
  Proof.
    intros; unfold reads_left, configuration_room_left; simpl.
    rewrite H; autorewrite with size'; simpl.
    destruct (conf_state q2); Lia.lia.
  Qed.

  Definition advance (steps: nat) (t1: state_template a) (s: P4A.state_ref St) :=
    match s with
    | inl s =>
      let st := P4A.t_states a s in
      if Compare_dec.le_gt_dec (size a s) (t1.(st_buf_len) + steps)
      then List.map (fun r => {| st_state := r; st_buf_len := 0 |}) (possible_next_states _ _ _ st)
      else [{| st_state := t1.(st_state); st_buf_len := t1.(st_buf_len) + steps |}]
    | inr b => [{| st_state := inr false; st_buf_len := 0 |}]
    end.

  Lemma advance_correct_active q bs s:
    conf_state (a := interp a) q = inl s ->
    1 <= length bs <= configuration_room_left q ->
    List.In (conf_to_state_template (follow q bs))
      (advance (length bs)
        (conf_to_state_template q)
        (st_state (conf_to_state_template q))).
  Proof.
    intros.
    unfold configuration_room_left in H0.
    unfold advance; simpl; rewrite H in *.
    autorewrite with size' in H0; simpl in H0.
    destruct (Compare_dec.le_gt_dec _ _).
    - assert (P4A.size a s = conf_buf_len q + length bs) by Lia.lia.
      unfold conf_to_state_template.
      apply List.in_map_iff; eexists; split.
      + rewrite conf_buf_len_follow_transition; [reflexivity|].
        rewrite H; now autorewrite with size'.
      + simpl.
        apply conf_state_follow_transition_syntactic; auto.
        rewrite H.
        autorewrite with size'.
        simpl.
        lia.
    - left.
      unfold conf_to_state_template.
      f_equal.
      + rewrite conf_state_follow_fill; auto.
        rewrite H.
        now autorewrite with size'.
      + rewrite conf_buf_len_follow_fill; auto.
        rewrite H.
        now autorewrite with size'.
  Qed.

  Lemma advance_correct_passive q1 bs b:
    conf_state q1 = inr b ->
    1 <= length bs ->
    List.In (conf_to_state_template (follow q1 bs))
      (advance (length bs)
        (conf_to_state_template q1)
        (st_state (conf_to_state_template q1))).
  Proof.
    intros.
    destruct bs.
    - simpl in H0.
      Lia.lia.
    - autorewrite with follow.
      unfold advance; simpl.
      rewrite H.
      unfold conf_to_state_template.
      rewrite follow_done.
      + left.
        f_equal.
        erewrite conf_buf_len_done.
        reflexivity.
        rewrite follow_done.
        reflexivity.
        eapply conf_state_step_done.
        exact H.
      + now apply conf_state_step_done with (h := b).
  Qed.

  Lemma advance_correct q1 bs:
    (forall s, conf_state q1 = inl s ->
               length bs <= configuration_room_left q1) ->
    1 <= length bs ->
    List.In (conf_to_state_template (follow q1 bs))
      (advance (length bs)
        (conf_to_state_template q1)
        (st_state (conf_to_state_template q1))).
  Proof.
    intros.
    destruct (conf_state q1) eqn:?.
    - apply advance_correct_active with (s := s); intuition.
    - now apply advance_correct_passive with (b := b).
  Qed.

  Lemma interp_state_template_definite:
    forall q t,
      interp_state_template (a := a) t q ->
      conf_to_state_template q = t.
  Proof.
    intros.
    now apply interp_state_template_dichotomy with (c := q).
  Qed.

  Lemma advance_correct':
    forall prev1 prev2 succ1 c1 c2 bs,
      length bs = reads_left (prev1, prev2) ->
      interp_state_template prev1 c1 ->
      interp_state_template prev2 c2 ->
      interp_state_template succ1 (follow c1 bs) ->
      List.In succ1 (advance (reads_left (prev1, prev2))
                             prev1
                             (st_state prev1)).
  Proof.
    intros.
    rewrite <- H.
    rewrite
      <- interp_state_template_definite with (t := prev1) (q := c1),
      <- interp_state_template_definite with (t := succ1) (q := follow c1 bs)
      by auto.
    rewrite
      <- interp_state_template_definite with (t := prev1) (q := c1),
      <- interp_state_template_definite with (t := prev2) (q := c2)
      in H by auto.
    apply advance_correct; setoid_rewrite H.
    - intros.
      now apply reads_left_upper_bound with (s := s).
    - apply reads_left_lower_bound.
  Qed.

  Definition reachable_pair_step' (r0: state_pair) : nat * state_pairs :=
    let '(t1, t2) := r0 in
    let s1 := t1.(st_state) in
    let s2 := t2.(st_state) in
    let steps := reads_left r0 in
    (steps, List.list_prod (advance steps t1 s1)
                           (advance steps t2 s2)).

  Lemma reachable_step_backwards:
    forall st st' bs sts q1 q2,
      reachable_pair_step' st' = (length bs, sts) ->
      List.In st sts ->
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st; cs_st2 := snd st|}
                        (follow q1 bs)
                        (follow q2 bs) ->
      interp_conf_state (a:=a)
                        {|cs_st1 := fst st'; cs_st2 := snd st'|}
                        q1
                        q2.
  Proof.
    intros [st1 st2] [st1' st2'].
    unfold reachable_pair_step'.
    intros.
    set (k := reads_left (st1', st2')) in *.
    inversion H.
    subst sts.
    clear H.
    apply List.in_prod_iff in H0.
    unfold interp_conf_state; cbn; intuition.
    - admit.
    - admit.
  Admitted.

  Definition reaches (cur prev: state_template a * state_template a)
    : list (nat * (state_template a * state_template a)) :=
    let '(n, successors) := reachable_pair_step' prev in
    if List.In_dec (state_pair_eq_dec) cur successors
    then [(n, prev)]
    else [].

  Lemma reaches_prev:
    forall cur prev prev' size,
      List.In (size, prev') (reaches cur prev) ->
      prev' = prev.
  Proof.
    unfold reaches.
    intros.
    destruct (reachable_pair_step' _) in H.
    destruct (List.in_dec _ _) in H.
    - simpl in *; destruct H.
      + congruence.
      + tauto.
    - simpl in H; tauto.
  Qed.

  Lemma reachable_step_size:
    forall prev size s,
      reachable_pair_step' prev = (size, s) ->
      size = reads_left prev.
  Proof.
    unfold reachable_pair_step'.
    intros.
    destruct prev.
    congruence.
  Qed.

  Lemma reaches_length:
    forall size cur prev,
      List.In (size, prev) (reaches cur prev) ->
      size = reads_left prev.
  Proof.
    unfold reaches.
    intros.
    destruct (reachable_pair_step' _) eqn:?.
    destruct (List.in_dec _ _); simpl in *; [eauto with datatypes | tauto].
    destruct H; [|tauto].
    inversion H; subst.
    eapply reachable_step_size; eauto.
  Qed.

  Lemma reaches_exists:
    forall cur prev size l,
      reachable_pair_step' prev = (size, l) ->
      List.In cur l ->
      List.In (size, prev) (reaches cur prev).
  Proof.
    unfold reaches.
    intros.
    destruct (reachable_pair_step' _).
    inversion H; subst.
    destruct (List.in_dec _ _); [eauto with datatypes | tauto].
  Qed.

  Lemma follow_in_reaches:
    forall bs prev succ c1 c2,
      length bs = reads_left prev ->
      interp_state_template (fst prev) c1 ->
      interp_state_template (snd prev) c2 ->
      interp_state_template (fst succ) (follow c1 bs) ->
      interp_state_template (snd succ) (follow c2 bs) ->
      List.In (length bs, prev) (reaches succ prev).
  Proof.
    intros.
    unfold reaches.
    unfold reachable_pair_step'.
    destruct prev as (prev1, prev2).
    destruct succ as (succ1, succ2).
    simpl in H0, H1, H2, H3.
    destruct (List.in_dec state_pair_eq_dec _ _).
    - apply List.in_prod_iff in i; destruct i.
      left; now f_equal.
    - contradict n.
      apply List.in_prod_iff.
      split.
      + apply advance_correct' with (c1 := c1) (c2 := c2) (bs := bs); auto.
      + rewrite reads_left_commutative.
        apply advance_correct' with (c1 := c2) (c2 := c1) (bs := bs); auto.
        now rewrite reads_left_commutative.
  Qed.

  Definition reachable_pair_step (r0: state_pair) : state_pairs :=
    snd (reachable_pair_step' r0).

  Definition reachable_step (r: state_pairs) : state_pairs :=
    let r' := (List.concat (List.map reachable_pair_step r)) in
    List.nodup state_pair_eq_dec (r' ++ r).

  Definition reachable_states' := iter _ reachable_step.
    (* match fuel with
    | 0 => r
    | S fuel => reachable_step (reachable_states' fuel r)
    end. *)

  

  Lemma nodup_incl' {X: Type} {Heq: EqDec X eq}:
    forall (l1 l2: list X),
      List.incl l1 l2 <-> List.incl (List.nodup Heq l1) l2.
  Proof.
    split; intros.
    - induction l1; try easy.
      simpl.
      destruct (List.in_dec Heq a0 l1).
      + apply IHl1.
        apply List.incl_cons_inv in H.
        intuition.
      + apply List.incl_cons_inv in H.
        apply List.incl_cons; try easy.
        intuition.
    - induction l1; try easy.
      apply List.incl_cons.
      + apply H.
        simpl.
        destruct (List.in_dec Heq a0 l1).
        * now apply List.nodup_In.
        * now left.
      + apply IHl1.
        simpl in H.
        destruct (List.in_dec Heq a0 l1).
        * assumption.
        * apply List.incl_cons_inv in H.
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
      now apply H.
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
    - replace (S f1 + f2) with (S (f1 + f2)) by lia.
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
    apply (H l0 (l3 ++ l2)).
    repeat rewrite List.app_assoc.
    f_equal.
    now repeat rewrite <- List.app_assoc.
  Qed.

  Lemma chain_trivial:
    forall p, chain [p].
  Proof.
    unfold chain; intros.
    apply (f_equal (@List.length state_pair)) in H.
    repeat rewrite List.app_length in H.
    simpl in H.
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
      apply (f_equal (@List.rev state_pair)) in H1.
      repeat rewrite List.rev_app_distr in H1.
      simpl in H1.
      inversion H1.
      now subst.
    - apply (f_equal (@List.removelast state_pair)) in H1.
      replace [p; p'] with ([p] ++ [p']) in H1 by easy.
      rewrite List.app_assoc in H1.
      rewrite List.removelast_last in H1.
      rewrite List.app_assoc in H1.
      rewrite List.removelast_app in H1 by easy.
      apply (H l1 (List.removelast (s :: l2))).
      rewrite <- List.app_assoc in H1.
      exact H1.
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
    - inversion_clear H.
      constructor.
      + contradict H0.
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
    - simpl in H.
      exists nil, nil, p.
      simpl; repeat split; auto.
      + apply chain_trivial.
      + apply nodup_trivial.
    - simpl in H.
      unfold reachable_step in H.
      rewrite List.nodup_In, List.in_app_iff in H.
      destruct H; [|now apply IHfuel].
      rewrite <- List.flat_map_concat_map,
              List.in_flat_map_Exists,
              List.Exists_exists in H.
      destruct H as [p' [? ?]].
      apply IHfuel in H.
      destruct H as [lpre' [lpost' [s [? [? [? ?]]]]]].
      destruct (List.in_dec state_pair_eq_dec p ([s] ++ lpost')).
      + apply List.in_split in i.
        destruct i as [l1 [l2 ?]].
        exists l1.
        destruct l1.
        * exists nil, s.
          simpl in *.
          repeat split; auto.
          -- now inversion_clear H4.
          -- apply chain_trivial.
          -- apply nodup_trivial.
        * simpl in *.
          exists (l1 ++ [p]), s.
          repeat split; auto.
          -- now inversion_clear H4.
          -- rewrite H4 in H2.
             apply chain_split_left with (l2 := l2).
             inversion_clear H4.
             simpl.
             now rewrite <- List.app_assoc.
          -- rewrite H4 in H3.
             inversion_clear H4.
             eapply nodup_split_left with (l4 := l2).
             now rewrite <- List.app_comm_cons, <- List.app_assoc.
      + exists (lpre' ++ [p']), (lpost' ++ [p]), s.
        repeat split; auto.
        * rewrite List.app_comm_cons.
          now f_equal.
        * rewrite List.app_comm_cons, H1.
          rewrite <- List.app_assoc.
          apply chain_cons; auto.
          now rewrite <- H1.
        * rewrite List.app_comm_cons.
          apply NoDup_app; auto.
          -- apply nodup_trivial.
          -- intros.
             contradict n.
             inversion_clear n; try contradiction.
             now subst.
          -- intros.
             inversion_clear H4; try contradiction.
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
        inversion H0.
        now subst.
      + apply (f_equal (@List.length state_pair)) in H0.
        rewrite List.app_length in H0.
        simpl in H0.
        lia.
    - simpl.
      induction lpre using List.rev_ind.
      + simpl in H0.
        inversion H0.
        apply (f_equal (@List.rev state_pair)) in H4.
        simpl in H4.
        rewrite List.rev_unit in H4.
        discriminate.
      + rewrite List.app_length; simpl.
        replace (length lpost + 1) with (S (length lpost)) by lia; simpl.
        unfold reachable_step.
        rewrite List.nodup_In.
        rewrite List.in_app_iff.
        left.
        rewrite <- List.flat_map_concat_map.
        rewrite List.in_flat_map_Exists.
        rewrite List.Exists_exists.
        simpl in H0.
        exists x0.
        split.
        * eapply IHlpost with (s := s); auto.
          -- rewrite <- List.removelast_last with (a := x) at 1.
             rewrite <- List.removelast_last with (a := p).
             rewrite <- List.app_comm_cons.
             rewrite H0.
             reflexivity.
          -- unfold chain in *; intros.
             apply H1 with (l1 := l1) (l2 := l2 ++ [x]).
             rewrite List.app_comm_cons, H2.
             now repeat rewrite <- List.app_assoc.
        * rewrite H0 in H1.
          rewrite <- List.app_assoc in H1.
          simpl in H1.
          unfold chain in H1.
          apply H1 with (l1 := lpre) (l2 := nil).
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
               (List.seq 0 (size a s))
      ) (List.map inl (enum St1) ++ List.map inr (enum St2)).

  Definition valid_state_template (t: state_template a) :=
    match st_state t with
    | inr _ => st_buf_len t = 0
    | inl s => st_buf_len t < size a s
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
    - simpl in H0.
      destruct (Compare_dec.le_gt_dec _ _).
      + rewrite List.in_map_iff in H0.
        destruct H0 as [? [? ?]].
        rewrite <- H0; simpl.
        destruct x; auto.
        apply a.
      + destruct H0; try contradiction.
        rewrite <- H0.
        simpl.
        rewrite Heqs.
        unfold P4A.t_states in g.
        simpl in H0.
        simpl.
        lia.
   - destruct H0.
     + now rewrite <- H0.
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
    unfold reachable_pair_step in H0.
    unfold reachable_pair_step' in H0.
    destruct p, p'.
    unfold snd in H0.
    apply List.in_prod_iff in H0.
    destruct H0.
    simpl in H; destruct H.
    simpl; split.
    - eapply valid_state_templates_closed with (t := s); auto.
      exact H0.
    - eapply valid_state_templates_closed with (t := s0); auto.
      exact H1.
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
    unfold valid_state_pair in H.
    simpl in H.
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
      + apply (valid_state_pairs_closed H).
        now apply H0 with (l1 := nil) (l2 := l).
      + destruct H1.
        * subst; auto.
        * apply IHl with (p := a0); auto.
          unfold chain in *.
          intros.
          eapply H0 with (l1 := p :: l1) (l2 := l2).
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
    apply reachability_sound in H0.
    destruct H0 as [lpre [lpost [s [? [? [? ?]]]]]].
    eapply reachability_complete with (s := s).
    - auto.
    - exact H1.
    - exact H2.
    - apply List.NoDup_incl_length; [now inversion H3 |].
      clear H1.
      induction lpost using List.rev_ind; intros; try easy.
      apply List.incl_app.
      + apply IHlpost.
        * now apply chain_split_left with (l2 := [x]).
        * now eapply nodup_split_left with (l2 := [x]).
      + unfold List.incl; intros.
        destruct H1; [subst | easy].
        apply valid_state_pairs_accurate.
        apply chain_preserve_valid with (p := s) (l := lpost ++ [a1]); auto.
        rewrite List.in_app_iff; right.
        apply List.in_eq.
  Qed.

  Lemma reachable_states_closed' (r: list state_pair) (p1 p2: state_pair):
    (forall p, List.In p r -> valid_state_pair p) ->
    List.In p1 (reachable_states' (length valid_state_pairs) r) ->
    List.In p2 (reachable_step [p1]) ->
    List.In p2 (reachable_states' (length valid_state_pairs) r).
  Proof.
    intros.
    apply reachable_states_bound with (fuel := S (length valid_state_pairs)); auto.
    unfold reachable_states'.
    fold (reachable_states' (length valid_state_pairs) r).
    revert H1; apply reachable_step_mono.
    unfold List.incl; intros.
    destruct H1; try contradiction; now subst.
  Qed.


  Scheme Equality for list.

  Definition length_eqb (l: state_pairs) (r: state_pairs) := Nat.eqb (length l) (length r).

  Definition reachable_states'' := iter' _ reachable_step length_eqb.

  Require Import Coq.Lists.List.
  Lemma length_nodup : 
    forall (A: Type) eq (xs ys: list A),
      length (List.nodup eq (xs ++ ys)) = length ys ->
      List.nodup eq (xs ++ ys) = ys.
  Proof.
    intros.
    induction ys.
    - erewrite app_nil_r in *.
      simpl in H.
      destruct (nodup eq xs).
      + exact eq_refl.
      + inversion H.
    - admit.
  Admitted.

  Require Import Coq.Arith.PeanoNat.
  Lemma reachable_step_length :
    forall x,
      length_eqb (reachable_step x) x = true <-> reachable_step x = x.
  Proof.
    intros.
    unfold length_eqb.
    erewrite Nat.eqb_eq.
    split; intros.
    - unfold reachable_step in *.
      erewrite length_nodup; auto.
    - rewrite H.
      exact eq_refl.
  Qed.

  Lemma reachable_equal : 
    forall n s, reachable_states' n s = reachable_states'' n s.
  Proof.
    unfold reachable_states', reachable_states''.
    intros.
    eapply iter_iter'.
    exact reachable_step_length.
  Qed.

  Lemma reachable_states_closed (r: list state_pair) (p1 p2: state_pair):
    (forall p, List.In p r -> valid_state_pair p) ->
    List.In p1 (reachable_states'' (length valid_state_pairs) r) ->
    List.In p2 (reachable_step [p1]) ->
    List.In p2 (reachable_states'' (length valid_state_pairs) r).
  Proof.
    intros.
    erewrite <- reachable_equal in *.
    eapply reachable_states_closed'; eauto.
  Qed.

  Definition build_state_pairs s1 s2 : state_pairs := 
    let s := ({| st_state := inl (inl s1); st_buf_len := 0 |},
              {| st_state := inl (inr s2); st_buf_len := 0 |}) in
    [s].

  Definition reachable_states_fp := fp state_pairs.
  Definition reachable_states_wit s1 s2 : state_pairs -> Type := 
    fp_wit _ reachable_step (build_state_pairs s1 s2).

  Definition reachable_states s1 s2 : state_pairs :=
    reachable_states'' (length valid_state_pairs) (build_state_pairs s1 s2).

  Lemma reachable_states_wit_conv : 
    forall s1 s2 ss,
      reachable_states_wit s1 s2 ss ->
      reachable_states s1 s2 = ss.
  Admitted.

  Definition reachable_pair rs (q1 q2: conf) : Prop :=
    List.Exists (fun '(t1, t2) =>
                   interp_state_template t1 q1 /\
                   interp_state_template t2 q2)
                rs.

End ReachablePairs.

