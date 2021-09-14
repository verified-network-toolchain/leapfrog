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

  Inductive header: Set :=
  | HPref
  | HDest
  | HSrc
  | HProto.

  Scheme Equality for header.

  Global Program Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.

  Global Program Instance header_finite: @Finite header _ header_eqdec :=
    {| enum := [HPref; HDest; HSrc; HProto] |}.
  Next Obligation.
    repeat constructor; eauto with datatypes;
    cbn;
    intuition congruence.
  Qed.
  Next Obligation.
    destruct x; intuition congruence.
  Qed.

  Definition states (s: state) := 
    match s with 
    | SPref => {| st_op := OpExtract 64 (HRVar HPref);
                  st_trans := TGoto _ (inl SDest) |}
    | SDest => {| st_op := OpExtract 48 (HRVar HDest);
                  st_trans := TGoto _ (inl SSrc) |}
    | SSrc => {| st_op := OpExtract 48 (HRVar HSrc);
                  st_trans := TGoto _ (inl SProto) |}
    | SProto => {| st_op := OpExtract 16 (HRVar HProto);
                  st_trans := P4A.TSel (CExpr (EHdr (HRVar HProto)))
                    [{| sc_pat := PExact (VBits [true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false]);
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

  Inductive header :=
  | HdrVar.

  Global Instance header_eqdec: EquivDec.EqDec header eq.
    vm_compute.
    intros.
    left.
    destruct x; destruct x0; trivial.
  Defined.

  Global Program Instance header_finite: @Finite header _ header_eqdec :=
    {| enum := [HdrVar] |}.
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

  Definition states (s: state) :=
    match s with
    | Parse =>
      {| st_op := (OpExtract 176 (HRVar HdrVar));
        st_trans := P4A.TSel (CExpr (ESlice (EHdr (HRVar HdrVar)) 176 160))
                              [{| sc_pat := PExact (VBits [true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false]);
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
  Global Instance header_eq_dec: EquivDec.EqDec header eq :=
    ltac:(typeclasses eauto).
  Global Instance header_finite: @Finite header _ header_eq_dec :=
    ltac:(typeclasses eauto).

  Definition aut := sum Reference.aut Combined.aut.
End RefComb.
