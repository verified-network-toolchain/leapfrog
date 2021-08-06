Require Import Poulet4.P4automata.Examples.ProofHeader.
Require Import Poulet4.P4automata.Examples.BabyIP.

From Hammer Require Import Tactics.


Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    extend_bisim a wp i R C;
    idtac R;
    idtac C
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    skip_bisim a wp i R C;
    idtac R;
    idtac C
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  end.

Ltac give_goal :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
       let H := fresh "H" in
       assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
                  interp_crel i R q1 q2 -> interp_conf_rel C q1 q2);
       idtac; [rewrite filter_entails by (typeclasses eauto);
        simpl;
        cbn;
        unfold interp_conf_rel, interp_conf_state, interp_state_template;
        simpl;
        intros [[s1 st1] buf1] [[s2 st2] buf2] Hprem Hl1 Hl2 [Hs1 Hs2] valu;
        simpl in *
       |]
  end.

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
                  interp_crel i R q1 q2 -> interp_conf_rel C q1 q2))
         by (
           rewrite filter_entails by (typeclasses eauto);
           simpl;
           cbn;
           unfold interp_conf_rel, interp_conf_state, interp_state_template;
           simpl;
           match goal with |- ?G => idtac "admitting" G end; admit
         );
         pose (t := wp a C);
         idtac C;
         eapply PreBisimulationExtend with (H0 := right H) (W := t);
         [ tauto | reflexivity |];
         compute in t;
         simpl (_ ++ _);
         unfold t;
         clear t;
         clear H
  end.

Ltac skip_bisim' :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
       let H := fresh "H" in
       assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
                  interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
         by (match goal with |- ?G => idtac "admitting" G end; admit);
       eapply PreBisimulationSkip with (H0:=left H);
       [ exact I | ];
       clear H
  end.

Lemma prebisim_babyip:
  pre_bisimulation BabyIP.aut
                   (WPSymLeap.wp r_states)
                   (Reachability.reachable_pair r_states)
                   nil
                   (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)
                   (inl (inl BabyIP1.Start), [], [])
                   (inl (inr BabyIP2.Start), [], []).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.
  extend_bisim'.
  extend_bisim'.
Admitted.
