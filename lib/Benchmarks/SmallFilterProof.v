Require Import Leapfrog.Bisimulations.Semantic.
Require Import Leapfrog.Bisimulations.LeapsProofs.
Require Import Leapfrog.Bisimulations.WPLeapsProofs.
Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.SmallFilter.


Notation H := (IncrementalBits.header + BigBits.header).
Notation A := IncrementalSeparate.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        IncrementalSeparate.aut
                        IncrementalBits.Start
                        BigBits.Parse).

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (IncrementalBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (IncrementalBits.Suf, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Pref, FirstOrderConfRelSimplified.Bits 1)
  (BigBits.Suf, FirstOrderConfRelSimplified.Bits 1).
*)

Lemma drop_antecedent:
  forall P Q: Prop, P -> (P -> Q) <-> Q.
Proof.
  tauto.
Qed.

Ltac crunch_foterm_ctx :=
  match goal with
  | H: context[interp_fm ?v ?g] |- _ =>
      let temp := fresh "temp" in
      set (temp := g) in H; vm_compute in temp; subst temp;
      (let temp := fresh "temp1" in
       set (temp := v) in H; vm_compute in temp; subst temp)
  end.

Ltac compile_fm H :=
  erewrite simplify_entailment_correct
    with (equiv0:=RelationClasses.eq_equivalence)
         (St_eq_dec:=@Sum.St_eq_dec _ _ _ _ _ _)
    in H;
  rewrite compile_simplified_entailment_correct in H;
  rewrite FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr in H;
  erewrite FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr in H;
  erewrite CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct in H;
  crunch_foterm_ctx;
  (* these could be invariants and somehow avoided completely
     or if they have to be done it could all be done with reflection *)
  try rewrite !drop_antecedent with (P := state_template_sane _) in H
      by apply P4A.P4A.cap';
  try rewrite !drop_antecedent with (P := state_template_sane _) in H
      by (unfold state_template_sane;
          simpl;
          autorewrite with size';
          cbv;
          autorewrite with op_fmapH; Lia.lia);
  rewrite !drop_antecedent with (P := top' _ _ _ _ _ _ _ _) in H
      by repeat match goal with
                | |- ?x = ?x \/ _ => exact (or_introl eq_refl)
                | |- ?x = ?y \/ _ => apply or_intror
                | |- _ => cbn
                end.

Ltac remember_iff name hyp term :=
  set (name := term);
  assert (hyp: name <-> term) by reflexivity;
  clearbody name.

Ltac decide_entailment H P HP P_orig e :=
  let Horig := fresh "Horig" in
  set (P_orig := e);
  remember_iff P HP e;
  assert (Horig: P_orig <-> P)
    by (rewrite HP; reflexivity);
  compile_fm HP;
  match goal with
  | HP: P <-> interp_fm ?v ?f |- _ =>
      time "smt check neg" check_interp_neg (interp_fm v f);
      idtac "UNSAT";
      assert (~ P_orig) by (rewrite -> Horig; rewrite -> HP; apply dummy_pf_false)
  | HP: P <-> interp_fm ?v ?f |- _ =>
      time "smt check pos" check_interp_pos (interp_fm v f);
      idtac "SAT";
      assert (P_orig) by (rewrite -> Horig; rewrite -> HP; apply dummy_pf_true)
  | |- _ => idtac "undecided goal :("
  end;
  clear Horig.

Lemma small_filter_equiv:
  lang_equiv_state
    (P4A.interp IncrementalBits.aut)
    (P4A.interp BigBits.aut)
    IncrementalBits.Start
    BigBits.Parse.
Proof.
  eapply Sum.sum_thing; [typeclasses eauto | typeclasses eauto |].
  unfold lang_equiv_state.
  intros.
  match goal with
  | |- lang_equiv ?c1t ?c2t =>
    set (cr0 := {| cr_st :=
                     {| cs_st1 := conf_to_state_template (a:=A) c1t;
                        cs_st2 := conf_to_state_template (a:=A) c2t; |};
                   cr_ctx := BCEmp;
                   cr_rel := btrue; |});
      unfold conf_to_state_template in cr0; simpl in cr0;
      set (c1 := c1t);
      set (c2 := c2t)
  end.
  assert (interp_conf_rel' cr0 c1 c2).
  {
    unfold interp_conf_rel'.
    cbv; intuition.
    autorewrite with interp_store_rel.
    tauto.
  }
  generalize dependent c1.
  generalize dependent c2.
  subst cr0.
  intros.
  apply bisimilar_implies_equiv.
  apply bisimilar_iff_bisimilar_with_leaps.
  eapply wp_leaps_implies_bisim_leaps with
    (s1 := IncrementalBits.Start)
    (s2 := BigBits.Parse).
  2:{
    (* The second goal is fairly easy to discharge; this should be doable
       for proofs like this in general. *)
    unfold WPLeapsProofs.top.
    vm_compute Reachability.reachable_states.
    inversion H.
    inversion H0.
    erewrite !Reachability.interp_state_template_definite by eauto.
    vm_compute conf_to_state_template.
    do 6 right.
    left.
    reflexivity.
  }
  vm_compute Reachability.reachable_states.
  vm_compute mk_init.
  repeat match goal with
         | |- pre_bisimulation ?a ?r_states ?wp ?R (?C :: _) _ _ =>
             let H := fresh "H" in
             let P := fresh "P" in
             let HP := fresh "HP" in
             let P_orig := fresh "P_orig" in
             decide_entailment H P HP P_orig (interp_entailment a
                                                                (fun q1 q2 =>
                                                                   top' _ _ _ _ _ r_states
                                                                        (conf_to_state_template q1)
                                                                        (conf_to_state_template q2))
                                                                ({| e_prem := R; e_concl := C |}));
             match goal with
             | HN: ~ P_orig |- _ =>
                 time "extending" (extend_bisim' HN; clear HN)
             | H: P_orig |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
                 time "skipping" (skip_bisim' H; clear H; try clear C)
             end;
             clear P HP P_orig
         end.
  match goal with
  | |- pre_bisimulation _ ?r_states _ _ _ _ _ =>
        apply PreBisimulationClose;
         match goal with
         | H:interp_conf_rel' ?C ?q1 ?q2
           |- interp_crel _ _ ?P ?q1 ?q2 =>
               let H0 := fresh "H0" in
               assert
                (H0 :
                 interp_entailment'
                   (fun q1 q2 =>
                    top' _ _ _ _ _ r_states (conf_to_state_template q1)
                      (conf_to_state_template q2)) {| e_prem := P; e_concl := C |}) by
                (eapply simplify_entailment_correct';
                  eapply compile_simplified_entailment_correct'; simpl; 
                  intros; eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
                  eapply compile_simplified_fm_bv_correct; crunch_foterm;
                  match goal with
                  | |- ?X => time "smt check pos" check_interp_pos X; apply dummy_pf_true
                  end); apply H0; auto; unfold top', conf_to_state_template; 
                destruct q1, q2; vm_compute in H;
                repeat match goal with
                       | H:_ /\ _ |- _ => idtac H; destruct H
                       end; subst; simpl; tauto
         end
  end.
Time Qed.

Check small_filter_equiv.
Print Assumptions small_filter_equiv.
