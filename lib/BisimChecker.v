Require Import Leapfrog.Bisimulations.WPLeaps.
Require Import Leapfrog.CompileConfRelSimplified.
Require Import Leapfrog.CompileFirstOrderConfRelSimplified.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.FinType.
Require Import Leapfrog.LangEquivToPreBisim.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Utils.Tactics.
Require Import Leapfrog.Utils.FunctionalFP.
Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

Require Leapfrog.WP.
Require Leapfrog.Reachability.

Require Import Coq.Arith.PeanoNat.
Import List.ListNotations.

Local Declare ML Module "mirrorsolve".

Require Import Leapfrog.CompileBitVec.

Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
  ({| cr_st :=
        {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
           cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
      cr_ctx := ctx;
      cr_rel := b|}) (at level 10).
Notation btrue := (BRTrue _ _).
Notation bfalse := (BRFalse _ _).
Notation "a ⇒ b" := (BRImpl a b) (at level 40).

Section BisimChecker.
  Set Implicit Arguments.
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> nat).

  Notation St := (St1 + St2)%type.
  Variable (a: P4A.t St Hdr_sz).

  Definition sum_not_accept1 (a: P4A.t (St1 + St2) Hdr_sz) (s: St1) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (St1 + St2) Hdr_sz) (s: St2) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (St1 + St2) Hdr_sz) : crel a :=
    List.concat (List.map (sum_not_accept1 a) (enum St1)
                          ++ List.map (sum_not_accept2 a) (enum St2)).

  Definition reachable_pair_to_partition '((s1, s2): Reachability.state_pair a)
    : crel a :=
    match s1.(st_state) with
    | inl st =>
      [BCEmp, ⟨inl st, s1.(st_buf_len)⟩ ⟨inr true, 0⟩ ⊢ bfalse]
    | inr st =>
      []
    end
      ++
      match s2.(st_state) with
      | inl st =>
        [BCEmp, ⟨inr true, 0⟩ ⟨inl st, s2.(st_buf_len)⟩ ⊢ bfalse]
      | inr st =>
        []
      end.

  Definition reachable_pairs_to_partition (r: Reachability.state_pairs a)
    : crel a :=
    List.concat (List.map reachable_pair_to_partition r).

  Definition states_match (c1 c2: conf_rel (Hdr_finite:=Hdr_finite) a) : bool :=
    if conf_states_eq_dec c1.(cr_st) c2.(cr_st)
    then true
    else false.

  Definition state_ref_eqb (x y: state_ref (P4A.interp a)) : bool :=
    match x, y with
    | inl x, inl y => if St_eq_dec x y then true else false
    | inr true, inr true => true
    | inr false, inr false => true
    | _, _ => false
    end.

  Definition st_eqb (x y: state_template a) : bool :=
    andb (Nat.eqb (st_buf_len x) (st_buf_len y))
         (state_ref_eqb (st_state x) (st_state y)).

  Definition st_pair_eqb (x y: state_template a * state_template a) : bool :=
    andb (st_eqb (fst x) (fst y))
         (st_eqb (snd x) (snd y)).

  Fixpoint in_R (x: state_template a * state_template a) (R: list (state_template a * state_template a)) : bool :=
    match R with
    | nil => false
    | x' :: R' =>
        if st_pair_eqb x x'
        then true
        else in_R x R'
    end.

  Lemma in_In :
    forall (R: list (state_template a * state_template a)) (x: state_template a * state_template a),
      List.In x R <-> (in_R x R = true).
  Proof.
    intros;
    induction R; simpl.
    - split; intros H; inversion H.
    - destruct (st_pair_eqb _ _) eqn:?; unfold st_pair_eqb in *.
      + split; intros; try exact eq_refl.
        destruct x, a0; cbn in Heqb.
        left.
        symmetry in Heqb.
        eapply Bool.andb_true_eq in Heqb.
        destruct Heqb.
        unfold st_eqb, state_ref_eqb in *.
        eapply Bool.andb_true_eq in H0, H1.
        destruct H0, H1.
        destruct s, s0, s1, s2; simpl in *.
        apply EqNat.beq_nat_eq in H1.
        apply EqNat.beq_nat_eq in H0.
        subst.
        repeat match goal with
               | H: context[ match ?x with | _  => _ end] |- _ => destruct x
               | _ => congruence
               | _ => simpl in *
               | _ => subst
               end.
      + split; intros.
        * apply IHR.
          destruct H; auto.
          exfalso.
          subst.
          unfold st_eqb in *.
          unfold state_ref_eqb in *.
          repeat match goal with
                 | H: (?X && ?Y)%bool = false |- _ =>
                     apply Bool.andb_false_elim in H;
                     destruct H
                 end;
            rewrite ?Nat.eqb_refl in *;
            try congruence;
            repeat match goal with
                   | H: context[ match ?x with | _  => _ end] |- _ => destruct x
                   | _ => congruence
                   | _ => simpl in *
                   | _ => subst
                   end.
        * right; now apply IHR.
  Qed.

  (* Links together all the correctness theorems in the compilation pipeline. *)
  Lemma compilation_corr:
    forall (R: list (Reachability.state_pair a)) (E: entailment a),
      interp_entailment a
        (fun q1 q2 : configuration (ConfRel.P4A.interp a) =>
          top' _ _ _ _ a R (conf_to_state_template q1) (conf_to_state_template q2))
        E
      <->
      let E' := (se_st (simplify_entailment E)) in
      (state_template_sane (cs_st1 E') ->
        state_template_sane (cs_st2 E') ->
        top' _ _ _ _ a R (cs_st1 E') (cs_st2 E') ->
        interp_fm
          (m := BV.fm_model)
          (VEmp _ _)
          ( fmap_fm FirstOrderBitVec.sig BV.sig FirstOrderBitVec.fm_model BV.fm_model conv_functor (@conv_fun_arrs) (@conv_rel_arrs) (@conv_forall_op)
          (compile_fm
              (FirstOrderConfRelSimplified.simplify_eq_zero_fm
                (FirstOrderConfRelSimplified.simplify_concat_zero_fm
                    (compile_simplified_entailment (simplify_entailment E))))))).
  Proof.
    intros.
    erewrite simplify_entailment_correct
      with (equiv0:=RelationClasses.eq_equivalence)
          (St_eq_dec:=@Sum.St_eq_dec _ _ St1_eq_dec _ _ St2_eq_dec);
    erewrite compile_simplified_entailment_correct;
    erewrite FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr;
    erewrite FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
    erewrite CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;
    erewrite conv_corr;
    eapply iff_refl.
  Qed.

End BisimChecker.

Ltac hashcons_list xs :=
  match xs with
  | ?x :: ?xs =>
    hashcons_list xs;
    let v := fresh "v" in
    set (v := x) in |- * at 1

  | ?x :: nil =>
    let v := fresh "v" in
    set (v := x) in |- * at 1
  | _ => idtac
  end.

Ltac extend_bisim HN use_hc :=
  match goal with
  | |- pre_bisimulation ?a ?r_states _ _ (?C :: _) _ _ =>
    pose (t := WP.wp r_states C);
    time "apply extend" (apply PreBisimulationExtend with (H := right HN) (W := t));
    [ trivial | subst t; reflexivity |];
    clear HN;
    time "wp compute" vm_compute in t;
    subst t;
    match goal with
    | |- pre_bisimulation _ _ _ (_ :: ?R') (?X ++ _) _ _ =>
      let r := fresh "R'" in
      time "set R'" (set (r := R'));
      match use_hc with
      | true => time "hashcons" (hashcons_list X)
      | false => idtac
      end;
      time "simplify append" (simpl (_ ++ _))
    end
  end.

Ltac skip_bisim H0 :=
  time "apply skip" (apply PreBisimulationSkip with (H:=left H0));
  [ exact I | ];
  clear H0.

Ltac crunch_foterm :=
  match goal with
  | |- interp_fm ?v ?g =>
    let temp := fresh "temp" in set (temp := g);
    vm_compute in temp;
    subst temp;
    let temp := fresh "temp1" in set (temp := v);
    vm_compute in temp;
    subst temp
  end.

Ltac crunch_foterm_ctx :=
  match goal with
  | H: _ <-> interp_fm _ ?g |- _ =>
    let temp := fresh "temp" in
    set (temp := g) in H; vm_compute in temp; subst temp
  end.

Ltac compile_fm H el er :=
  time "compilation correct" erewrite compilation_corr with (St1_eq_dec := el) (St2_eq_dec := er) in H;
  simpl in H;
  (* these could be invariants and somehow avoided completely *)
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

Ltac remember_iff name hyp term :=
  time "setting in rem_iff" pose (name := term);
  time "proving name <-> term" assert (hyp: name <-> term) by eapply iff_refl;
  time "clearbody" clearbody name.

(* Unsound axioms to discharge goals cleared by the plugin. *)
Polymorphic Axiom dummy_pf_true:
  forall sig m c (v: valu sig m c) fm, interp_fm v fm.
Polymorphic Axiom dummy_pf_false:
  forall sig m c (v: valu sig m c) fm, ~ interp_fm v fm.

(* Decides a template-guarded entailment by compiling it to a first-order
   formula, shipping that off to the plugin, and admitting that if it clears
   the goal. The result will have the (possibly negated) entailment in the
   context if it was succesful. *)
Ltac decide_entailment_admit H P HP el er P_orig e :=
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
      time "asserting neg" assert (~ P_orig) by admit
  | HP: P <-> interp_fm ?v ?f |- _ =>
      time "smt check pos" check_interp_pos (interp_fm v f);
      idtac "SAT";
      time "asserting pos" assert (P_orig) by admit
  | |- _ => idtac "undecided goal :("
  end;
  time "clearing Horig" clear Horig.

(* Does the same as decide_entailment_admit, but uses an unsound axiom instead
   of admitting the goal cleared by our plugin. *)
Ltac decide_entailment_axiom H P HP el er P_orig e :=
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
  | HP: _ <-> interp_fm _ ?f |- _ => idtac "undecided goal :("; idtac f
  end;
  time "clearing Horig" clear Horig.

(* Initializes the search for a lang_equiv proof by converting it into a
   pre-bisimulation goal using the soundness theorem. Also pre-computes the
   set of reachable state template pairs. *)
Ltac init_bisim :=
  eapply lang_equiv_to_pre_bisim;
  time "init prebisim" (intros;
  unfold mk_init;
  erewrite Reachability.reachable_states_wit_conv; [
    | repeat econstructor | econstructor; solve_fp_wit
  ];
  simpl).

(* Runs the main loop of our algorithm, clearing a pre-bisimulation goal by
   repeatedly applying the PreBisimulationExtend constructor until there are
   no more formulas left in T. Verification conditions created this way will
   be admitted as long as they can be cleared by our plugin. *)
Ltac run_bisim_admit el er use_hc :=
  match goal with
  | |- pre_bisimulation ?a ?r_states ?wp ?R (?C :: _) _ _ =>
      let H := fresh "H" in
      let P := fresh "P" in
      let HP := fresh "HP" in
      let P_orig := fresh "P_orig" in
      decide_entailment_admit H P HP el er P_orig (interp_entailment a
                                                          (fun q1 q2 =>
                                                            top' _ _ _ _ _ r_states
                                                                  (conf_to_state_template q1)
                                                                  (conf_to_state_template q2))
                                                          ({| e_prem := R; e_concl := C |}));
      match goal with
      | HN: ~ P_orig |- _ =>
          time "extending" (extend_bisim HN use_hc; clear HN)
      | H: P_orig |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
          time "skipping" (skip_bisim H; clear H; try clear C)
      end;
      time "clearing all" clear P HP P_orig
  end.

(* Does the same as run_bisim_admit, but uses an axiom instead of admitting. *)
Ltac run_bisim_axiom el er use_hc :=
  match goal with
  | |- pre_bisimulation ?a ?r_states ?wp ?R (?C :: _) _ _ =>
      let H := fresh "H" in
      let P := fresh "P" in
      let HP := fresh "HP" in
      let P_orig := fresh "P_orig" in
      decide_entailment_axiom H P HP el er P_orig (interp_entailment a
                                                         (fun q1 q2 =>
                                                            top' _ _ _ _ _ r_states
                                                                 (conf_to_state_template q1)
                                                                 (conf_to_state_template q2))
                                                         ({| e_prem := R; e_concl := C |}));
      match goal with
      | HN: ~ P_orig |- _ =>
          time "extending" (extend_bisim HN use_hc; clear HN)
      | H: P_orig |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
          time "skipping" (skip_bisim H; clear H; try clear C)
      end;
      time "clearing all" clear P HP P_orig
  end.

(* Closes the pre-bisimulation search by applying the PreBisimulationClose
   constructor, and checking whether the remaining goal compiles to a formula
   that can be cleared by our plugin. Corresponds to the final step in the
   algorithm. *)
Ltac close_bisim_admit :=
  match goal with
  | |- pre_bisimulation _ ?r_states _ _ _ _ _ =>
    apply PreBisimulationClose;
    match goal with
    | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ _ ?P ?q1 ?q2 =>
      let H0 := fresh "H0" in
      assert (H0: interp_entailment' (fun q1 q2 =>
        top' _ _ _ _ _ r_states
            (conf_to_state_template q1)
            (conf_to_state_template q2)
      ) {| e_prem := P; e_concl := C |}) by (
        eapply simplify_entailment_correct';
        eapply compile_simplified_entailment_correct';

        simpl; intros;
        eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
        eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;
        eapply conv_corr;

        crunch_foterm;
        match goal with
        | |- ?X => time "smt check pos" check_interp_pos X; admit
        end
      );
      apply H0; auto;
      unfold top', conf_to_state_template;
      destruct q1, q2;
      vm_compute in H;
      repeat match goal with
             | H: _ /\ _ |- _ =>
               idtac H;
               destruct H
             end;
      subst;
      simpl; tauto
    end
  end.

(* Just like close_bisim_admit, but uses an axiom instead of admitting. *)
Ltac close_bisim_axiom :=
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
                  eapply compile_simplified_fm_bv_correct; 
                  eapply conv_corr; 
                  crunch_foterm;
                  match goal with
                  | |- ?X => time "smt check pos" check_interp_pos X; apply dummy_pf_true
                  end); apply H0; auto; unfold top', conf_to_state_template;
                destruct q1, q2; vm_compute in H;
                repeat match goal with
                       | H:_ /\ _ |- _ => destruct H
                       end; subst; simpl; tauto
         end
  end.

(* Tactic that solves a lang_equiv goal by discharging verfication conditions
   cleared by the plugin by applying an (unsound) axiom.

    arguments:
      el, er, eq_dec: functions for the left and right automata states
      use_hc, a bool to use or not use "hashconsing" of intermediate templates.
*)
Ltac solve_lang_equiv_state_axiom el er use_hc :=
  time "init phase" init_bisim;
  time "build phase" repeat run_bisim_axiom el er use_hc;
  time "close phase" close_bisim_axiom.

(* Tactic that solves a lang_equiv goal by admitting verfication conditions
   cleared by the plugin.

    arguments:
      el, er, eq_dec: functions for the left and right automata states
      use_hc, a bool to use or not use "hashconsing" of intermediate templates.
*)
Ltac solve_lang_equiv_state_admit el er use_hc :=
  time "init phase" init_bisim;
  time "build phase" repeat run_bisim_admit el er use_hc;
  time "close phase" close_bisim_admit.

(* Prints the number of clauses in the current pre-bisimulation goal. *)
Ltac print_rel_len :=
  let foo := fresh "foo" in
  let bar := fresh "bar" in
  match goal with
  | |- pre_bisimulation _ _ _ ?R _ _ _ =>
    set (foo := length R);
    assert (bar : foo = length R); [subst foo; trivial|]
  end;
  vm_compute in bar;
  match goal with
  | H: @eq nat _ ?X |- _ =>
    idtac "size of relation is:";
    idtac X
  end;
  clear foo;
  clear bar.
