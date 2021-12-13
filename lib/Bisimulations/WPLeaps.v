Require Import Coq.Lists.List.
Import List.ListNotations.

Require Import Leapfrog.P4automaton.
Require Import Leapfrog.FinType.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Relations.
Require Leapfrog.WP.

Require Import Coq.Classes.EquivDec.

Section WPLeaps.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  Notation St := ((St1 + St2)%type).

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (sz: Hdr -> nat).

  Variable (a: P4A.t St sz).

  Variable (wp: conf_rel a ->
                list (conf_rel a)).

  Notation conf := (configuration (P4A.interp a)).

  Variable (top: rel conf).
  Variable (top_closed: forall x y b, top x y -> top (step x b) (step y b)).

  Notation "⟦ x ⟧" := (interp_crel a top x).
  Notation "⦇ x ⦈" := (interp_conf_rel a x).
  Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
  Notation "R ⊨ S" := (interp_entailment a top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation "R ⫤ S" := (interp_entailment' top {| e_prem := R; e_concl := S |}) (at level 40).
  Notation δ := step.

  Reserved Notation "R ⇝ S" (at level 10).
  Inductive pre_bisimulation : crel a -> crel a -> rel conf :=
  | PreBisimulationClose:
      forall R q1 q2,
        ⟦R⟧ q1 q2 ->
        R ⇝ [] q1 q2
  | PreBisimulationSkip:
      forall (R T: crel a) (C: conf_rel a) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | left _ => True
        | _ => False
        end ->
        R ⇝ T q1 q2 ->
        R ⇝ (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T: crel a) (C: conf_rel a) (W: crel a) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | right _ => True
        | _ => False
        end ->
        W = wp C ->
        (C :: R) ⇝ (W ++ T) q1 q2 ->
        R ⇝ (C :: T) q1 q2
  where "R ⇝ T" := (pre_bisimulation R T).

  Lemma PreBisimulationExtend':
    forall (R T: crel a) (C: conf_rel a) (W: crel a) q1 q2 (H: {R ⊨ C} + {~(R ⊨ C)}),
    match H with
    | right _ => True
    | _ => False
    end ->
    W = wp C ->
    (add_strengthen_crel C R) ⇝ (W ++ T) q1 q2 ->
    R ⇝ (C :: T) q1 q2.
  Proof.
    intros.
    eapply PreBisimulationExtend with (H := H) (W := W); auto.
  Admitted.


  Fixpoint range (n: nat) :=
    match n with
    | 0 => []
    | S n => range n ++ [n]
    end.

  Definition not_accept1 (a: P4A.t St sz) (s: St) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition not_accept2 (a: P4A.t St sz) (s: St) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                               cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition init_rel (a: P4A.t St sz) : crel a :=
    List.concat (List.map (not_accept1 a) (enum St) ++
                          List.map (not_accept2 a) (enum St)).

  Definition sum_not_accept1 (a: P4A.t (St1 + St2) sz) (s: St1) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                               cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inl s))).

  Definition sum_not_accept2 (a: P4A.t (St1 + St2) sz) (s: St2) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a (inr s))).

  Definition sum_init_rel (a: P4A.t (St1 + St2) sz) : crel a :=
    List.concat (List.map (sum_not_accept1 a) (enum St1)
                          ++ List.map (sum_not_accept2 a) (enum St2)).
  Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
    ({| cr_st :=
          {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
             cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
        cr_ctx := ctx;
        cr_rel := b|}) (at level 10).
  Notation btrue := (BRTrue _ _).
  Notation bfalse := (BRFalse _ _).
  Notation "a ⇒ b" := (BRImpl a b) (at level 40).

  Definition not_equally_accepting (s: Reachability.state_pair a) : bool :=
    let '(s1, s2) := s in
    match s1.(st_state), s2.(st_state) with
    | inr true, inr true => false
    | inr true, _ => true
    | _, inr true => true
    | _, _ => false
    end.

  Definition mk_rel '((s1, s2): Reachability.state_pair a)
    : conf_rel a :=
    {| cr_st := {| cs_st1 := s1;
                   cs_st2 := s2 |};
       cr_ctx := BCEmp;
       cr_rel := bfalse |}.

  Definition mk_partition (r: Reachability.state_pairs a) : crel a :=
    List.map mk_rel (List.filter not_equally_accepting r).

  Definition mk_init (n: nat) s1 s2 :=
    List.nodup (@conf_rel_eq_dec _ _ _ _ _ _ _ _ a)
               (mk_partition (Reachability.reachable_states a n s1 s2)).

  Definition lift_l {X Y A} (f: X -> A) (x: X + Y) : A + Y :=
    match x with
    | inl x => inl (f x)
    | inr y => inr y
    end.

  Definition separated (q1 q2: conf) : Prop :=
    ((exists x, conf_state q1 = inl (inl x)) \/
     (exists y, conf_state q1 = inr y)) /\
    ((exists x, conf_state q2 = inl (inr x)) \/
     (exists y, conf_state q2 = inr y)).

  Definition topbdd (C: rel conf) : Prop :=
    forall q1 q2,
      C q1 q2 ->
      top q1 q2.

  Definition ctopbdd (C: crel a) : Prop :=
    forall r,
      In r C ->
      topbdd ⦇r⦈.

  Definition safe_wp_1bit : Prop :=
    forall C (q1 q2: conf),
      top q1 q2 ->
      ⟦wp C⟧ q1 q2 ->
      forall bit,
        ⦇C⦈ (δ q1 bit) (δ q2 bit).

  Definition wp_bdd :=
    forall C,
      topbdd ⦇C⦈ ->
      ctopbdd (wp C).
End WPLeaps.

Arguments pre_bisimulation {St1 St2 Hdr equiv2 Hdr_eq_dec Hdr_finite sz} a wp.
Arguments ctopbdd {St1 St2 Hdr equiv2 Hdr_eq_dec Hdr_finite sz} a top C.
Arguments topbdd {St1 St2 Hdr equiv2 Hdr_eq_dec Hdr_finite sz} a top C.
Arguments safe_wp_1bit {St1 St2 Hdr equiv2 Hdr_eq_dec Hdr_finite sz} a wp top.
Arguments wp_bdd {St1 St2 Hdr equiv2 Hdr_eq_dec Hdr_finite sz} a wp top.
