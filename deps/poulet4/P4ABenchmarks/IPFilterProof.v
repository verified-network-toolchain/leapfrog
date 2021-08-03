Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.IPFilter.
From Hammer Require Import Tactics.

Require Import SMTCoq.SMTCoq.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Lemma neg_impl: 
  forall (P Q: Prop),
    inhabited P ->
    ~ (P -> Q) <-> P /\ ~ Q.
Proof.
  intros.
  intuition.
Qed.

Lemma prebisim_ipfilter:
  pre_bisimulation IPFilter.aut
                   (WPSymLeap.wp (H:=_))
                   (separated _ _ _ IPFilter.aut)
                   nil
                   (mk_init 10 IPFilter.aut UDPCombined.Parse UDPInterleaved.ParseIP)
                   (inl (inl UDPCombined.Parse), [], [])
                   (inl (inr UDPInterleaved.ParseIP), [], []).
Proof.
  idtac "running ipfilter bisimulation".
  set (rel0 := mk_init 10 IPFilter.aut UDPCombined.Parse UDPInterleaved.ParseIP).
  cbv in rel0.
  subst rel0.
  time solve_bisim.
  time solve_bisim.
  time solve_bisim.
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: (forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit
  end.

  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end. 

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.
  
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)) by admit;
              pose (t := wp a C);
          eapply PreBisimulationExtend with (H0 := right H) (W := t);
          [ tauto | reflexivity |];
          compute in t;
          simpl (_ ++ _);
          unfold t;
          clear t; 
          clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
              interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
      by admit;
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.
  
  apply PreBisimulationClose.
  

  (* repeat (unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template).
  intuition eauto;
  firstorder (try congruence);
  sauto limit:5000. *)


(* 
  repeat (unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template).
    
  simpl (List.map interp_conf_rel _).
  unfold fold_right.
  unfold RelationClasses.relation_conjunction.
  unfold RelationClasses.predicate_intersection. 
  sauto.

  unfold Relations.interp_rels, separated, interp_store_rel.
  unfold map.
  simpl (List.fold_right _ _ _).
  unfold RelationClasses.relation_conjunction.
  unfold RelationClasses.predicate_intersection. 
  simpl.
  intuition.
  vm_compute.

  intuition; (try sauto) || (

    vm_compute;
    intros;

    repeat match goal with 
    | H: (exists _, _) |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    end;
    congruence
  ). *)

  admit.

Time Admitted.