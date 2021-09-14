Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.PreBisimulationSyntax.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Reference.
  Inductive state: Set :=
  | SPref
  | SDest
  | SSrc
  | SProto.

  Scheme Equality for state.

  Global Program Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [SPref; SDest; SSrc; SProto] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes;
    cbn;
    intuition congruence.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header: nat -> Set :=
  | HPref: header 1
  | HDest: header 1
  | HSrc: header 1
  | HProto: header 1.
  Derive Signature for header.

  Equations header_eq_dec: forall n, forall x y: header n, {x = y} + {x <> y} :=
    { header_eq_dec 1 HPref HPref := in_left;
      header_eq_dec 1 HDest HDest := in_left;
      header_eq_dec 1 HSrc HSrc := in_left;
      header_eq_dec 1 HProto HProto := in_left;
      header_eq_dec _ _ _ := in_right }.
  Next Obligation.
    dependent destruction wildcard.
  Qed.
  Next Obligation.
    dependent destruction wildcard.
  Qed.

  Global Program Instance header_eqdec (n: nat) : EquivDec.EqDec (header n) eq := header_eq_dec n.

  Global Program Instance header_finite: @Finite (P4A.H' header) _ (P4A.H'_eq_dec (H_eq_dec:=header_eqdec)) :=
    {| enum := [existT _ 1 HPref;
                existT _ 1 HDest;
                existT _ 1 HSrc;
                existT _ 1 HProto] |}.
  Next Obligation.
    repeat constructor; cbn; intuition.
  Qed.
  Next Obligation.
    destruct x.
    destruct h; tauto.
  Qed.

  Definition states (s: state) := 
    match s with 
    | SPref => {| st_op := OpExtract (existT _ 1 HPref);
                  st_trans := TGoto _ (inl SDest) |}
    | SDest => {| st_op := OpExtract (existT _ 1 HDest);
                  st_trans := TGoto _ (inl SSrc) |}
    | SSrc => {| st_op := OpExtract (existT _ 1 HSrc);
                  st_trans := TGoto _ (inl SProto) |}
    | SProto => {| st_op := OpExtract (existT _ 1 HProto);
                  st_trans := P4A.TSel (CExpr (EHdr (HRVar (existT _ 1 HProto))))
                    [{| sc_pat := PExact (VBits [true]);
                        sc_st := inr true |}]
                    (inr false) |}
    end.
  

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
  
End Reference. 

Module Combined.
  Inductive state :=
  | Parse.
  
  Global Instance state_eqdec: EquivDec.EqDec state eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.

  Global Program Instance state_finite: @Finite state _ state_eqdec :=
    {| enum := [Parse] |}.
  Next Obligation.
  repeat constructor;
    repeat match goal with
           | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
           | |- ~ List.In _ [] => apply List.in_nil
           | |- ~ List.In _ (_ :: _) => unfold not; intros
           | H: List.In _ (_::_) |- _ => inversion H; clear H
           | _ => discriminate
           end.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Inductive header: nat -> Set :=
  | HdrVar: header 4.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq.
    vm_compute.
    intros n x y.
    dependent destruction x.
    dependent destruction y.
    left.
    reflexivity.
  Defined.

  Global Program Instance header_finite:
    @Finite (P4A.H' header) _ (P4A.H'_eq_dec (H_eq_dec:=header_eqdec)) :=
    {| enum := [existT _ 4 HdrVar] |}.
  Next Obligation.
  repeat constructor;
    repeat match goal with
           | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
           | |- ~ List.In _ [] => apply List.in_nil
           | |- ~ List.In _ (_ :: _) => unfold not; intros
           | H: List.In _ (_::_) |- _ => inversion H; clear H
           | _ => discriminate
           end.
  Qed.
  Next Obligation.
    destruct x as [_ []]; tauto.
  Qed.

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := (OpExtract (existT _ 4 HdrVar));
        st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar (existT _ 4 HdrVar))) 4 3))
                              [{| sc_pat := PExact (VBits [true]);
                                  sc_st := inr true |}]
                              (inr (A := state) false) |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
  
End Combined.

Module RefComb.
  Definition state: Type := Sum.S Reference.state Combined.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H Reference.header Combined.header.
  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite (P4A.H' header) _ (P4A.H'_eq_dec (H_eq_dec:=header_eq_dec)).
  apply Sum.H_eq_dec.
    ltac:(typeclasses eauto).

  Definition aut := sum Reference.aut Combined.aut.
End RefComb.
