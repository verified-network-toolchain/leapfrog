Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized. 
Require Import Leapfrog.FirstOrderConfRelSimplified.

Ltac compile_fm H el er :=
  time "compilation correct" erewrite compilation_corr with (St1_eq_dec := el) (St2_eq_dec := er) in H; [
    | typeclasses eauto | typeclasses eauto | eapply check_fm_wf_corr; exact eq_refl
  ];
  simpl in H;
  (* these could be invariants and somehow avoided completely
      or if they have to be done it could all be done with reflection *)
  time "antecedents" match goal with
  | H0: _ <-> (?a -> ?b -> ?c -> ?d) |- _ =>
    erewrite drop_antecedent_3 with (A := a) in H0;
    [|
      vm_compute; repeat econstructor |
      vm_compute; repeat econstructor |
      eapply in_In; exact eq_refl
    ]

  end;
  crunch_foterm_ctx.

Ltac decide_entailment H P HP el er P_orig e :=
  let Horig := fresh "Horig" in
  pose (P_orig := e);
  time "remembering iff" remember_iff P HP e;
  time "Horig" assert (Horig: P_orig <-> P)
    by (rewrite HP; eapply iff_refl);
  time "compile fm" compile_fm HP el er;
  match goal with
  | HP: P <-> interp_fm ?v ?f |- _ =>
      time "smt check neg" check_interp_neg (interp_fm v f);
      idtac "UNSAT";
      time "asserting neg" assert (~ P_orig) by (rewrite -> Horig; rewrite -> HP; apply dummy_pf_false)
  | HP: P <-> interp_fm ?v ?f |- _ =>
     time "smt check pos" check_interp_pos (interp_fm v f);
      idtac "SAT";
      time "asserting pos" assert (P_orig) by (rewrite -> Horig; rewrite -> HP; apply dummy_pf_true)
  | |- _ => idtac "undecided goal :("
  end;
  time "clearing Horig" clear Horig.

Ltac run_bisim_axiom el er use_hc :=
  match goal with
  | |- pre_bisimulation ?a ?r_states ?wp ?R (?C :: _) _ _ =>
      let H := fresh "H" in
      let P := fresh "P" in
      let HP := fresh "HP" in
      let P_orig := fresh "P_orig" in
      decide_entailment H P HP el er P_orig (interp_entailment a
                                                         (fun q1 q2 =>
                                                            top' _ _ _ _ _ r_states
                                                                 (conf_to_state_template q1)
                                                                 (conf_to_state_template q2))
                                                         ({| e_prem := R; e_concl := C |}));
      match goal with 
      | HN: ~ P_orig |- _ =>
          time "extending" (extend_bisim' HN use_hc; clear HN)
      | H: P_orig |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
          time "skipping" (skip_bisim' H; clear H; try clear C)
      end;
      time "clearing all" clear P HP P_orig
  end.

Ltac solve_lang_equiv_state_axiom el er use_hc :=
  eapply lang_equiv_to_pre_bisim;
  time "init prebisim" (intros;
  unfold mk_init;
  erewrite Reachability.reachable_states_wit_conv; [
    | repeat econstructor | econstructor; solve_fp_wit
  ];
  simpl);
  time "build phase" run_bisim_axiom el er use_hc.
  (* ;
  time "close phase" close_bisim_axiom. *)


Lemma mpls_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Unrolled.aut)
    Plain.ParseMPLS
    Unrolled.ParseMPLS.
Proof.

  time "mpls no hc" solve_lang_equiv_state_axiom Plain.state_eqdec Unrolled.state_eqdec false.


  4: {
    eapply check_fm_wf_corr;
    exact eq_refl.
    3: {
      exact (@Sum.sum Plain.state Unrolled.state Plain.header Plain.sz
      Unrolled.header Unrolled.sz Plain.aut Unrolled.aut).
    }
    3: 
    4: exact eq_refl.
    all: typeclasses eauto.
    exact eq_refl.
    
  }
  (* time "mpls hc" solve_lang_equiv_state_axiom Plain.state_eqdec Unrolled.state_eqdec true. *)

Time Qed.

