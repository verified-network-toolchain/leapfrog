Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.ConfRel.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.Reachability.
Require Import Poulet4.P4automata.Bisimulations.WPLeaps.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.CompileConfRelSimplified.
Require Import Poulet4.P4automata.CompileFirstOrderConfRelSimplified.

Require Import Coq.Arith.PeanoNat.
Import List.ListNotations.


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

  Definition states_match (c1 c2: conf_rel (H_finite:=H_finite) a) : bool :=
    if conf_states_eq_dec c1.(cr_st) c2.(cr_st)
    then true
    else false.

  Lemma filter_entails:
    forall i R C,
      (forall q1 q2, interp_crel a i R q1 q2 -> interp_conf_rel a C q1 q2)
      <->
      (forall q1 q2, interp_crel a i (List.filter (states_match C) R) q1 q2 -> interp_conf_rel a C q1 q2).
  Proof.
  Admitted.

  Definition state_temp_prod_eqdec : forall (x y: state_template a * state_template a), {x = y} + {x <> y} :=
    fun x y => EquivDec.prod_eqdec _ _ x y. 

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


Ltac hashcons_list xs :=
  match xs with
  | ?x :: ?xs =>
    hashcons_list xs;
    let v := fresh "v" in
    set (v := x)

  | ?x :: nil =>
    let v := fresh "v" in
    set (v := x)
  | _ => idtac
  end.


Ltac extend_bisim r_states :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment a i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    let t := fresh "t" in
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right H) (W := t);
    [ trivial | subst t; reflexivity |];
    vm_compute in t;
    subst t;
    match goal with
    | |- pre_bisimulation _ _ _ (?R' :: ?R'') (?X ++ _) _ =>
      let r := fresh "R" in
      set (r := R');
      hashcons_list X;
      simpl (_ ++ _)
    end ]
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
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ _ =>
    pose (t := WP.wp r_states C);
    apply PreBisimulationExtend with (H0 := right HN) (W := t);
    [ trivial | subst t; reflexivity |];
    clear HN;
    time "wp compute" vm_compute in t;
    subst t;
    match goal with
    | |- pre_bisimulation _ _ _ (_ :: ?R') (?X ++ _) _ _ =>
      let r := fresh "R'" in
      set (r := R');
      hashcons_list X;
      simpl (_ ++ _)
    end
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
  | |- interp_fm ?v ?g =>
    let temp := fresh "temp" in set (temp := g);
    vm_compute in temp;
    subst temp;
    let temp := fresh "temp1" in set (temp := v);
    vm_compute in temp;
    subst temp
  end.

Declare ML Module "mirrorsolve".

Ltac verify_interp top top' :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment a top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := top');
      eapply compile_simplified_entailment_correct; simpl; intros;
      eapply FirstOrderConfRelSimplified.simplify_concat_zero_fm_corr;
      eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
      eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;


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
    | H : interp_entailment _ _ _ |- pre_bisimulation ?a _ _ ?R (?C :: _) _ _ =>
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
  | H: interp_entailment _ _ _  |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
    idtac "skipping"; skip_bisim' H; clear H; try clear C
  end.


  Fixpoint in_checker {A} (A_eq: forall (x y: A), ({x = y} + {x <> y})%type) (x: A) (xs : list A) : bool :=
    match xs with
    | nil => false
    | x' :: xs' => 
      if A_eq x' x then true else in_checker A_eq x xs'
    end.
  
  Lemma in_checker_conv : 
    forall A A_eq x xs, 
      (@in_checker A A_eq x xs = true) -> List.In x xs.
  Proof.
    intros.
    induction xs; [inversion H|].
    
    simpl in_checker in H.
    destruct (A_eq _ _).
    - econstructor; assumption.
    - eapply or_intror.
      eapply IHxs.
      assumption.
  Qed. 


Ltac close_bisim top' :=
  apply PreBisimulationClose;
  match goal with
  | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ ?top ?P ?q1 ?q2 =>
    let H0 := fresh "H0" in
    assert (H0: interp_entailment' top {| e_prem := P; e_concl := C |}) by (
      eapply simplify_entailment_correct' with (i := top');
      eapply compile_simplified_entailment_correct';

      simpl; intros;
      eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
      eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;

      crunch_foterm;
      match goal with
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    );
    apply H0; auto;
    unfold top, conf_to_state_template;
    destruct q1, q2;
    vm_compute in H;
    repeat match goal with
           | H: _ /\ _ |- _ =>
             idtac H;
             destruct H
           end;
    subst;
    simpl; tauto
  end.

Ltac close_bisim' top' := 
  eapply PreBisimulationClose;
  match goal with
  | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ ?top ?P ?q1 ?q2 =>
    let H0 := fresh "H0" in
    assert (H0: interp_entailment' top {| e_prem := P; e_concl := C |}) by (
      eapply simplify_entailment_correct' with (i := top');
      eapply compile_simplified_entailment_correct';

      simpl; intros;
      eapply FirstOrderConfRelSimplified.simplify_eq_zero_fm_corr;
      eapply CompileFirstOrderConfRelSimplified.compile_simplified_fm_bv_correct;

      crunch_foterm;
      match goal with
      | |- ?X => time "smt check pos" check_interp_pos X; admit
      end
    );
    eapply H0; 
    destruct q1, q2;
    vm_compute in H;
    repeat match goal with 
    | H: _ /\ _ |- _ => destruct H
    end;
    [
      apply in_checker_conv with (A_eq := fun x y => state_temp_prod_eqdec x y);
      unfold conf_to_state_template, P4automaton.conf_buf_len, P4automaton.conf_state;
    
      repeat match goal with 
      | H: _ = _ |- _ => erewrite <- H
      end;
      exact eq_refl
                    |
      split; [ vm_compute; (repeat split || assumption) | (intros; exact I)]
    ]
  end.

(* solves a header finiteness goal of the form:
List.NoDup
  [existT (fun n : nat => header n) 64 HPref;
  existT (fun n : nat => header n) 48 HDest;
  existT (fun n : nat => header n) 48 HSrc;
  existT (fun n : nat => header n) 16 HProto]

  which is an obligation for:

    @Finite {n & header n} _ header_eqdec'

  *)
Ltac solve_header_finite :=
  repeat constructor;
  unfold "~"; intros;
  repeat match goal with
  | H: List.In _ _ |- _ => destruct H
  | H: _ = _ |- _ => inversion H
  end.

(* solves a header eq_dec from a list of finite indices and decision procedures, e.g.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 32 h32_eq_dec) :: nil).
  Defined.

*)
Ltac solve_header_eqdec_ n x y indfuns :=
  match indfuns with
  | existT _ ?index ?f :: ?indfuns =>
    destruct (Nat.eq_dec n index); [
      subst; exact (f x y)  |
      solve_header_eqdec_ n x y indfuns
    ]
  | nil =>
    destruct x; exfalso; auto
  end.


