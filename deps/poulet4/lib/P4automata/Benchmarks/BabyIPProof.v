Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.FirstOrder.

From Hammer Require Import Tactics.

Notation H := (BabyIP1.header + BabyIP2.header).
Notation A := BabyIP.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        BabyIP.aut
                        200
                        BabyIP1.Start
                        BabyIP2.Start).

Ltac extend_bisim' :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment A i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend with (H0 := right H) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear H ]
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

Lemma forall_exists_demorgan: forall X P,
  (exists (x: X), ~P x) -> ~forall (x: X), P x.
Proof.
  intros.
  intro.
  destruct H.
  specialize (H0 x).
  contradiction.
Qed.

Lemma prebisim_babyip:
  pre_bisimulation
    A
    (WP.wp r_states)
    (fun c1 c2 => List.In (conf_to_state_template c1, conf_to_state_template c2) r_states)
    []
    (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)
    (P4automaton.MkConfiguration
      (Syntax.interp BabyIP.aut)
      (inl (inl BabyIP1.Start))
      0
      tt
      ltac:(eapply cap')
      nil)
    (P4automaton.MkConfiguration
      (Syntax.interp BabyIP.aut)
      (inl (inr BabyIP2.Start))
      0
      tt
      ltac:(eapply cap')
      nil).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.

  extend_bisim'.
  intro.
  rewrite -> simplify_entailment_correct with (i := (fun c1 c2 => List.In (c1, c2) r_states)) in H.
  Opaque List.In.
  simpl in H.
  unfold simplify_entailment in H; simpl in H.
  unfold simplify_crel, simplify_conf_rel in H; simpl in H.
  unfold interp_simplified_entailment in H; simpl in H.
  Transparent interp_simplified_crel.
  Transparent interp_simplified_conf_rel.
  unfold interp_simplified_crel, interp_simplified_conf_rel in H; simpl in H.
  Transparent interp_store_rel.
  unfold interp_store_rel in H.
  apply H.
  apply cap'.
  apply cap'.
  right.
  left.
  reflexivity.
  exact tt.
  exact tt.
  admit.
  admit.
  exact I.
  exact tt.
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  skip_bisim'.
  skip_bisim'.
  skip_bisim'.
  apply PreBisimulationClose.
  cbn.
  rewrite compile_conf_rel_correct.
  unfold compile_conf_rel.
  unfold FImpl; simpl.
  autorewrite with interp_fm; simpl.
  autorewrite with mod_fns; simpl;
  split.
  - left.
    easy.
  - rewrite compile_conf_rel_correct.
    unfold compile_conf_rel, FImpl; simpl.
    autorewrite with interp_fm; simpl.
    autorewrite with mod_fns; simpl.
Admitted.
