Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.

Import List.ListNotations.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.CompileConfRelSimplified.
Require Import Poulet4.P4automata.CompileFirstOrderConfRelSimplified.

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
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Notation S:=(S1 + S2)%type.
  Variable (a: P4A.t S H).

  Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel a :=
    List.concat (List.map (sum_not_accept1 a) (enum S1)
                          ++ List.map (sum_not_accept2 a) (enum S2)).

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

  (*
  Lemma no_state:
    forall (a: P4A.t S H) i R (S: conf_rel a),
      (forall (q1 q2: configuration (P4A.interp a)) (_ : interp_crel a i R q1 q2),
          interp_conf_rel a S q1 q2)
      <->
      (forall st1 (buf1: Ntuple.n_tuple bool S.(cr_st).(cs_st1).(st_buf_len)) st2
         (buf2: Ntuple.n_tuple bool S.(cr_st).(cs_st2).(st_buf_len)),
          let q1 := (S.(cr_st).(cs_st1).(st_state), st1, Ntuple.t2l buf1) in
          let q2 := (S.(cr_st).(cs_st2).(st_state), st2, Ntuple.t2l buf2) in
          interp_crel a i R q1 q2 ->
          forall valu : bval (cr_ctx S), interp_store_rel (cr_rel S) valu q1 q2).
  Proof.
    intros.
    split; intros.
    - unfold interp_conf_rel in *.
      simpl.
      intros.
  Admitted.
  *)

  Definition states_match {S H} {a: P4A.t S H} {S_eq_dec: EquivDec.EqDec S eq} {H_eq_dec: forall n, EquivDec.EqDec (H n) eq} (c1 c2: conf_rel a) : bool :=
    if conf_states_eq_dec c1.(cr_st) c2.(cr_st)
    then true
    else false.

  Lemma filter_entails:
    forall (a: P4A.t S H) i R C,
      (forall q1 q2, interp_crel a i R q1 q2 -> interp_conf_rel a C q1 q2)
      <->
      (forall q1 q2, interp_crel a i (List.filter (states_match C) R) q1 q2 -> interp_conf_rel a C q1 q2).
  Proof.
  Admitted.

End BisimChecker.

Lemma forall_exists:
  forall {A B} (P: A -> B -> Prop),
  (exists x y, ~ P x y) ->
  ~ (forall x y, P x y).
Proof.
  firstorder.
Qed.

Lemma double_neg:
  forall {A B} (P: A -> B -> Prop),
  (exists x y, P x y) ->
  (exists x y, ~ (P x y -> False)).
Proof.
  intros.
  destruct H as [x [y H]].
  exists x.
  exists y.
  intuition.
Qed.

Lemma split_univ:
  forall (A B : Type) (P : A * B -> Prop),
    (forall (x : A) (y : B), P (x, y)) <-> (forall x : A * B, P x).
Proof.
  firstorder.
  destruct x.
  firstorder.
Qed.

Lemma exists_unused:
  forall A,
    inhabited A ->
    forall P: Prop,
    exists (_: A), P <-> P.
Proof.
  intros.
  inversion H.
  firstorder.
Qed.
Lemma flip_ex_impl:
  forall A B (P Q: A -> B -> Prop),
    (exists x y, P x y /\ ~ Q x y) ->
    (exists x y, ~ (P x y -> Q x y)).
Proof.
  firstorder.
Qed.


Ltac extend_bisim r_states :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment a i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right H) (W := t);
    [ trivial | tauto |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t]
  end.

Ltac skip_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: interp_entailment a i ({| e_prem := R; e_concl := C |}));
    [idtac |
      apply PreBisimulationSkip with (H0:=left H);
      [ exact I | ];
      clear H
    ]
  end.

Ltac extend_bisim' HN r_states :=
  match goal with
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ =>
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right HN) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear HN
  end.

Ltac skip_bisim' H :=
  apply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac size_script :=
  unfold Syntax.interp;
  autorewrite with size';
  vm_compute;
  repeat constructor.


Ltac crunch_foterm :=
  match goal with
  | |- interp_fm _ ?g =>
    let temp := fresh "temp" in set (temp := g);
    vm_compute in temp;
    subst temp
  end.

Declare ML Module "mirrorsolve".

Ltac verify_interp top top' :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: interp_entailment a top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := top');
      eapply compile_simplified_entailment_correct;
      [ once typeclasses eauto | once typeclasses eauto | once typeclasses eauto |];
      eapply FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr;
      [ once typeclasses eauto | once typeclasses eauto |];

      time "reduce goal" crunch_foterm;

      match goal with
      | |- ?X => time "smt check neg" check_interp_neg X
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    |]
  end;
  let n:= numgoals in
  tryif ( guard n = 2) then
    match goal with
    | |- interp_fm _ _ => admit
    | H : interp_entailment _ _ _ |- pre_bisimulation ?a _ _ ?R (?C :: _) _ =>
      clear H;
      let HN := fresh "HN" in
      assert (HN: ~ (interp_entailment a top ({| e_prem := R; e_concl := C |}))) by admit
    end
  else idtac.

Ltac run_bisim top top' r_states :=
  verify_interp top top';
  match goal with
  | HN: ~ (interp_entailment _ _ _ ) |- _ =>
    idtac "extending"; extend_bisim' HN r_states; clear HN
  | H: interp_entailment _ _ _  |- _ =>
    idtac "skipping"; skip_bisim' H; clear H
  end.

Ltac close_bisim top' :=
  apply PreBisimulationClose;
  eapply simplify_entailment_correct' with (i := top');
  eapply compile_simplified_entailment_correct';
  [ once typeclasses eauto | once typeclasses eauto | once typeclasses eauto |];
  eapply FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr;
  [ once typeclasses eauto | once typeclasses eauto |];
  crunch_foterm;
  match goal with
  | |- ?X => time "smt check pos" check_interp_pos X; admit
  end.
