Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.ConfRel.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.Bisimulations.Algorithmic.

Section WPLeaps.

  (* State identifiers. *)
  Variable (S1: Type).
  Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
  Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

  Variable (S2: Type).
  Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
  Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

  Notation S := ((S1 + S2)%type).

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq}.
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

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
  Inductive pre_bisimulation : crel a -> crel a -> conf_rel a -> Prop :=
  | PreBisimulationClose:
      forall R S,
        R ⫤ S ->
        R ⇝ [] S
  | PreBisimulationSkip:
      forall (R T: crel a) (C: conf_rel a) S (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | left _ => True
        | _ => False
        end ->
        R ⇝ T S ->
        R ⇝ (C :: T) S
  | PreBisimulationExtend:
      forall (R T: crel a) (C: conf_rel a) (W: crel a) S (H: {R ⊨ C} + {~(R ⊨ C)}),
        match H with
        | right _ => True
        | _ => False
        end ->
        W = wp C ->
        (C :: R) ⇝ (W ++ T) S ->
        R ⇝ (C :: T) S
  where "R ⇝ T" := (pre_bisimulation R T).

  Fixpoint range (n: nat) :=
    match n with
    | 0 => []
    | Datatypes.S n => range n ++ [n]
    end.

  Definition not_accept1 (a: P4A.t S H) (s: S) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                               cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition not_accept2 (a: P4A.t S H) (s: S) : crel a :=
    List.map (fun n =>
                {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                               cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                   cr_rel := BRFalse _ BCEmp |})
             (range (P4A.size a s)).

  Definition init_rel (a: P4A.t S H) : crel a :=
    List.concat (List.map (not_accept1 a) (enum S) ++
                          List.map (not_accept2 a) (enum S)).

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
    List.nodup (@conf_rel_eq_dec _ _ _ _ _ _ a)
               (mk_partition
                  (Reachability.reachable_states a n s1 s2)).

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
Arguments pre_bisimulation {S1 equiv0 S1_eq_dec S2 equiv1 S2_eq_dec H equiv2 H'_eq_dec} a wp.

Arguments ctopbdd {_ _ _ _ _ _ _ _ _} a top C.
Arguments topbdd {_ _ _ _ _ _ _ _ _} a top C.
Arguments safe_wp_1bit {_ _ _ _ _ _ _ _ _} a wp top.
Arguments wp_bdd {_ _ _ _ _ _ _ _ _} a wp top.
