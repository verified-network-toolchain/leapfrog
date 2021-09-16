Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.FirstOrder.

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
                  interp_crel a i R q1 q2 -> interp_conf_rel a C q1 q2));
    [ idtac |
    pose (t := WPSymLeap.wp r_states a C);
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
    BabyIP.aut
    (WPSymLeap.wp r_states)
    (Reachability.reachable_pair r_states)
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
  setoid_rewrite compile_conf_rel_correct.
  apply forall_exists_demorgan; eexists.
  apply forall_exists_demorgan; eexists.
  cbn.
  2: { typeclasses eauto. }
  unfold compile_conf_rel.
  unfold FImpl; simpl.
  autorewrite with interp_fm; simpl.
  autorewrite with mod_fns; simpl.
  intro.
  destruct H; intuition.
  apply List.Exists_cons_hd; simpl.
  unfold interp_state_template; intuition.
  (* At this point it's clear that configurations like this exist... you just
     need to construct a dummy store to prove it.

     There's also some more junk about finiteness of header types that we need
     to resolve, though, and I'm not sure how. *)
  1-5: admit.

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
