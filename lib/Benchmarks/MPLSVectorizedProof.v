Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.MPLSVectorized.


Lemma drop_antecedent_3:
  forall (A B C D : Prop),
  A -> 
  B -> 
  C -> 
  (A -> B -> C -> D) <-> D.
Proof.
  intros.
  do 3 (erewrite drop_antecedent; eauto).
  eapply iff_refl.
Qed.


Ltac compile_fm' H el er :=
  time "compilation correct" erewrite compilation_corr with (St1_eq_dec := el) (St2_eq_dec := er) in H;
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
  

Ltac compile_fm H el er :=
  time "compilation correct" erewrite compilation_corr with (St1_eq_dec := el) (St2_eq_dec := er) in H;
  do 2 (erewrite drop_antecedent in H ; [|vm_compute; repeat econstructor]);
  erewrite drop_antecedent in H; [|eapply in_In; exact eq_refl];
  crunch_foterm_ctx.

Ltac decide_entailment H P HP el er P_orig e :=
  let Horig := fresh "Horig" in
  pose (P_orig := e);
  time "remembering iff" remember_iff P HP e;
  time "Horig" assert (Horig: P_orig <-> P)
    by (rewrite HP; eapply iff_refl);
  compile_fm' HP el er.
  (* time "local compile fm" compile_fm HP el er. *)

Lemma mpls_equiv:
  lang_equiv_state
    (P4A.interp Plain.aut)
    (P4A.interp Unrolled.aut)
    Plain.ParseMPLS
    Unrolled.ParseMPLS.
Proof.

  solve_lang_equiv_state Plain.state_eqdec Unrolled.state_eqdec.

  (* eapply lang_equiv_to_pre_bisim;
  time "init prebisim" (intros;
  unfold mk_init;
  erewrite Reachability.reachable_states_wit_conv; [
    | repeat econstructor | econstructor; solve_fp_wit
  ];
  simpl).


  match goal with
  | |- pre_bisimulation ?a ?r_states ?wp ?R (?C :: _) _ _ =>
      let H := fresh "H" in
      let P := fresh "P" in
      let HP := fresh "HP" in
      let P_orig := fresh "P_orig" in
      decide_entailment H P HP Plain.state_eqdec Unrolled.state_eqdec P_orig (interp_entailment a
                                                         (fun q1 q2 =>
                                                            top' _ _ _ _ _ r_states
                                                                 (conf_to_state_template q1)
                                                                 (conf_to_state_template q2))
                                                         ({| e_prem := R; e_concl := C |}))
      (* match goal with
      | HN: ~ P_orig |- _ =>
          time "extending" (extend_bisim' HN; clear HN)
      | H: P_orig |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
          time "skipping" (skip_bisim' H; clear H; try clear C)
      end;
      time "clearing all" clear P HP P_orig *)
  end. *)

Time Qed.

