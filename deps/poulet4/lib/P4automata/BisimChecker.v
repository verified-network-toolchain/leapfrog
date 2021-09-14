Require Import Coq.Relations.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4automata.Bisimulations.
Require Poulet4.P4automata.Sum.
Import Bisimulations.SynPreSynWP.

Import List.ListNotations.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.


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
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Notation S:=(S1 + S2)%type.

  Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel (S1 + S2) H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel (S1 + S2) H := 
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel (S1 + S2) H := 
    List.concat (List.map (sum_not_accept1 a) (enum S1)
                          ++ List.map (sum_not_accept2 a) (enum S2)).

  Definition reachable_pair_to_partition '((s1, s2): Reachability.state_pair _ _)
    : crel (S1 + S2) H :=
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

  Definition reachable_pairs_to_partition (r: Reachability.state_pairs _ _)
    : crel (S1 + S2) H :=
    List.concat (List.map reachable_pair_to_partition r).

  (*
  Lemma no_state:
    forall (a: P4A.t S H) i R (S: conf_rel S H),
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
 
  Definition states_match {S H} {S_eq_dec: EquivDec.EqDec S eq} (c1 c2: conf_rel S H) : bool :=
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

Ltac pbskip :=
  apply PreBisimulationSkip;
  [intros;
   cbn in *;
   unfold interp_conf_rel, interp_store_rel, interp_conf_state in *;
   simpl in *;
   tauto|].

From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
From Hammer Require Import Hammer.

Ltac pbskip_hammer :=
  apply PreBisimulationSkip;
    [intros [[s1 st1] buf1] [[s2 st2] buf2];
     repeat (unfold interp_crel,
             interp_conf_rel,
             interp_conf_state,
             interp_store_rel,
             interp_bit_expr,
             interp_store_rel,
             interp_state_template,
             RelationClasses.relation_conjunction,
             Relations.interp_rels
             || cbn);
     solve [sauto]|].

Ltac solve_bisim' :=
  match goal with
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  | |- pre_bisimulation _ _ _ _ (_::_) _ _ =>
    pbskip_hammer
  | |- pre_bisimulation ?a ?wp _ _ (?C::_) _ _ =>
    let t := fresh "tmp" in
    pose (t := wp a C);
    apply PreBisimulationExtend with (W:=t); [reflexivity|];
    cbv in t;
    unfold t;
    clear t;
    simpl (_ ++ _)
  | |- _ => progress simpl
  end.

Ltac pbskip_plain :=
    apply PreBisimulationSkip;
     [ intros; cbn in *; unfold interp_conf_rel, interp_store_rel, interp_conf_state, interp_state_template in *;
        simpl in *;
      subst;
      intros;
      intuition;
      repeat 
        match goal with
        | [ X : P4automaton.configuration _ |- _ ] => destruct X as [[? ?] l]; destruct l
        | [ X : _ * _ |- _ ] => destruct X
        end;
        simpl in *; try solve [simpl in *; congruence]
        |].
  
Ltac solve_bisim_plain :=
    match goal with
    | |- context[WPSymLeap.wp _ _] =>
      progress (
          unfold WPSymLeap.wp at -1;
          autounfold with wp;
          unfold WPSymLeap.wp_op;
          simpl)
    | |- pre_bisimulation _ _ _ _ [] _ _ =>
      apply PreBisimulationClose
    | |- pre_bisimulation _ _ _ _ (_::_) _ _ =>
      pbskip_plain; [idtac]
    | |- pre_bisimulation ?a ?wp _ _ (?C::_) _ _ =>
      let t := fresh "tmp" in
      pose (t := wp a C);
      apply PreBisimulationExtend with (W:=t); [reflexivity|];
      cbv in t;
      subst t
    | |- _ => progress simpl
    end.

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

Ltac find v :=
  match goal with
  | v := ?value : _ |- _ => value
  end.

Ltac break_store2 h0 h1 := 
  repeat match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    cut (exists y0 y1,
                P ([(h0, P4A.VBits y0);
                    (h1, P4A.VBits y1)]));
    [ intros [x0 [x1 ?]];
      exists ([(h0, P4A.VBits x0);
          (h1, P4A.VBits x1)]);
      eauto
      | trivial
    ];
    repeat eexists
  | |- (forall (x: P4A.store ?H), _) -> False =>
      intros
  | H: forall (x: P4A.store ?H), @?P x |- _ =>
      assert (forall y0 y1,
                  P ([(h0, P4A.VBits y0);
                      (h1, P4A.VBits y1)])); [
      cbn; sauto | 
      sauto
    ]
  end.

Ltac break_store4 h0 h1 h2 h3 := 
  repeat match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    cut (exists y0 y1 y2 y3,
                P ([(h0, P4A.VBits y0);
                    (h1, P4A.VBits y1);
                    (h2, P4A.VBits y2);
                    (h3, P4A.VBits y3)]));
    [ intros [x0 [x1 [x2 [x3 ?]]]];
      exists ([(h0, P4A.VBits x0);
          (h1, P4A.VBits x1);
          (h2, P4A.VBits x2);
          (h3, P4A.VBits x3)]);
      eauto
      | trivial
    ];
    repeat eexists
  | |- (forall (x: P4A.store ?H), _) -> False =>
      intros
  | H: forall (x: P4A.store ?H), @?P x |- _ =>
      assert (forall y0 y1 y2 y3,
                  P ([(h0, P4A.VBits y0);
                      (h1, P4A.VBits y1);
                      (h2, P4A.VBits y2);
                      (h3, P4A.VBits y3)])); [
      cbn; sauto | 
      sauto
    ]
  end.

Ltac break_store :=
  match goal with
  | |- context[ P4A.store ?H ] =>
    let hs := fresh "hdrs" in
    pose (hs := enum H);
    cbv in hs;
    match find hs with
    | [?h0; ?h1] => break_store2 h0 h1
    | [?h0; ?h1; ?h2; ?h3] => break_store4 h0 h1 h2 h3
    | _ => idtac hs
    end
  end.

(*
Ltac disprove_sat a i :=
  rewrite (filter_entails (a:=a)) by (typeclasses eauto);
  simpl;
  rewrite (no_state i) by (typeclasses eauto);
  repeat (unfold interp_conf_rel, interp_conf_state, interp_state_template, interp_store_rel || cbn);
  eapply forall_exists;
  repeat (setoid_rewrite <- split_univ; cbn);
  repeat (setoid_rewrite <- split_ex; cbn);
  (solve [sauto | unfold not; now break_store]).

Ltac extend_bisim a wp i R C :=
      let H := fresh "H" in
      assert (H: ~(forall q1 q2 : P4automaton.configuration (P4A.interp a),
                 interp_crel i R q1 q2 -> interp_conf_rel C q1 q2))
        by (disprove_sat a i);
        pose (t := wp a C);
        eapply PreBisimulationExtend with (H0 := right H) (W := t);
        [ tauto | reflexivity |];
        compute in t;
        simpl (_ ++ _);
        unfold t;
        clear t; 
        clear H.

Ltac prove_sat :=
  unfold interp_crel;
  unfold interp_conf_rel;
  unfold interp_conf_state, interp_state_template;
  simpl;
  sauto.

Ltac skip_bisim a wp i R C :=
  let H := fresh "H" in
  assert (H: forall q1 q2 : P4automaton.configuration (P4A.interp a),
             interp_crel i R q1 q2 -> interp_conf_rel C q1 q2)
    by prove_sat;
  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac solve_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    extend_bisim a wp i R C
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    skip_bisim a wp i R C
  | |- pre_bisimulation _ _ _ _ [] _ _ =>
    apply PreBisimulationClose
  end.

Ltac build_store hdrs P store :=
  idtac hdrs;
  idtac P;
  idtac store;
  match hdrs with
  | nil => constr:(P store)
  | ?h :: ?hdrs' =>
    let x := fresh "h" in
    let old_store := find store in
    clear store;
    set (store := (h, x) :: old_store);
    build_store hdrs' constr:(exists y, P store) store
  end.

Ltac simp_exists_store :=
  match goal with
  | |- exists (x: P4A.store ?H), @?P x =>
    pose (hdrs := FinType.enum H);
    cbv in hdrs;
    let store := fresh "store" in
    set (store := []: P4A.store H);
    cut (ltac:(build_store ltac:(find hdrs) P store))
  end.
*)
