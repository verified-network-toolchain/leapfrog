Require Import Leapfrog.FinType.
Require Import Leapfrog.P4automaton.
Require Import Leapfrog.ConfRel.
Require Leapfrog.WP.
Require Leapfrog.Reachability.
Require Import Leapfrog.Bisimulations.WPLeaps.
Require Import MirrorSolve.FirstOrder.
Require Import Leapfrog.FirstOrderConfRel.
Require Import Leapfrog.CompileConfRel.
Require Import Leapfrog.CompileConfRelSimplified.
Require Import Leapfrog.CompileFirstOrderConfRelSimplified.

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

  Definition states_match (c1 c2: conf_rel (Hdr_finite:=Hdr_finite) a) : bool :=
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
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment a i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    let t := fresh "t" in
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend' with (H0 := right H) (W := t);
    [
      typeclasses eauto 1 | typeclasses eauto 1 | trivial | trivial | subst t; reflexivity |
      let v := fresh "v" in
      set (v := add_strengthen_crel _ _);
      vm_compute in v;
      subst v
    ];
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
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
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
    time "apply extend" (apply PreBisimulationExtend with (H := right HN) (W := t));
    [ trivial | subst t; reflexivity |];
    clear HN;
    time "wp compute" vm_compute in t;
    subst t;
    match goal with
    | |- pre_bisimulation _ _ _ (_ :: ?R') (?X ++ _) _ _ =>
      let r := fresh "R'" in
      time "set R'" (set (r := R'));
      time "hashcons" (hashcons_list X);
      time "simplify append" (simpl (_ ++ _))
    end
  end.

Ltac extend_bisim'' HN r_states :=
  match goal with
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ _ =>
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend' with (H0 := right HN) (W := t);
    [
      typeclasses eauto 1 | typeclasses eauto 1 | trivial | trivial | subst t; reflexivity |
      let v := fresh "v" in
      set (v := add_strengthen_crel _ _);
      vm_compute in v;
      subst v
    ];
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


Ltac skip_bisim' H0 :=
  time "apply skip" (apply PreBisimulationSkip with (H:=left H0));
  [ exact I | ];
  clear H0.

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

Ltac verify_interp' top top' L :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment a top ({| e_prem := R; e_concl := C |}));
    [
      eapply L;

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
  time "verify_interp" (verify_interp top top');
  match goal with
  | HN: ~ (interp_entailment _ _ _ ) |- _ =>
    time "extending" (extend_bisim' HN r_states; clear HN)
  | H: interp_entailment _ _ _  |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
    time "skipping" (skip_bisim' H; clear H; try clear C)
  end.

Ltac run_bisim' top top' r_states L :=
  verify_interp' top top' L;
  match goal with
  | HN: ~ (interp_entailment _ _ _ ) |- _ =>
    time "extending" (extend_bisim' HN r_states; clear HN)
  | H: interp_entailment _ _ _  |- pre_bisimulation _ _ _ _ (?C :: _) _ _ =>
    time "skipping" (skip_bisim' H; clear H; try clear C)
  end.


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

Ltac close_bisim top' :=
  apply PreBisimulationClose;
  match goal with
  | H: interp_conf_rel' ?C ?q1 ?q2|- interp_crel _ ?top ?P ?q1 ?q2 =>
    let H := fresh "H" in
    assert (H: interp_entailment' top {| e_prem := P; e_concl := C |}) by (
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
    apply H; [cbv; trivial | auto]
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