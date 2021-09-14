Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.BabyIP.

From Hammer Require Import Tactics.

Notation H := (BabyIP1.header + BabyIP2.header).
Notation A := BabyIP.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states BabyIP.aut 200 BabyIP1.Start BabyIP2.Start).


Ltac extend_bisim' :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
                  interp_crel a i R q1 q2 -> interp_conf_rel a C q1 q2))
    by (
      cbn;
      unfold interp_conf_rel, interp_conf_state, interp_state_template;
      simpl;
      match goal with |- ?G => idtac "admitting" G end; admit
    );
    pose (t := WPSymLeap.wp r_states a C);
    eapply PreBisimulationExtend with (H0 := right H) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear H
  end.

Ltac skip_bisim' :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
       let H := fresh "H" in
       assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
                  interp_crel a i R q1 q2 -> interp_conf_rel a C q1 q2)
         by (match goal with |- ?G => idtac "admitting" G end; admit);
       eapply PreBisimulationSkip with (H0:=left H);
       [ exact I | ];
       clear H
  end.

Ltac size_script :=
  unfold Syntax.interp;
  autorewrite with size';
  vm_compute;
  repeat constructor.

Obligation Tactic := size_script.
Program Lemma prebisim_babyip:
  pre_bisimulation 
    BabyIP.aut 
    (WPSymLeap.wp r_states) 
    (Reachability.reachable_pair r_states)
    (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)
    (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)
    (P4automaton.MkConfiguration 
      (Syntax.interp BabyIP.aut)
      (inl (inl BabyIP1.Start))
      0
      tt
      _
      nil)
    (P4automaton.MkConfiguration 
      (Syntax.interp BabyIP.aut)
      (inl (inr BabyIP2.Start))
      0
      tt
      _
      nil).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.
  unfold eq_ind_r.
  simpl.

  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  extend_bisim'.
  skip_bisim'.
  skip_bisim'.
  skip_bisim'.
  apply PreBisimulationClose.
  unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template.
  simpl List.map.
  autorewrite with interp_store_rel.
  unfold Relations.interp_rels.

  simpl List.fold_right.
  simpl RelationClasses.relation_conjunction.
  unfold RelationClasses.relation_conjunction.
  unfold RelationClasses.predicate_intersection.

  (* vm_compute.

  repeat split.

  all: try sauto.

  unfold Ntuple.n_tuple_slice.

  sauto. *)
Admitted.
