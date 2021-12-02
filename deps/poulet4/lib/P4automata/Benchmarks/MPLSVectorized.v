Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.

Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Notations.
Require Import Poulet4.P4automata.BisimChecker.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module Plain.
  Inductive state :=
  | ParseMPLS
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS; ParseUDP] |}.
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
  | HdrMPLS
  | HdrUDP.

  Definition sz (h: header) : nat :=
    match h with
    | HdrMPLS => 32
    | HdrUDP => 64
    end.

  Scheme Equality for header.

  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.

  Global Instance header_finite': @Finite header _ header_eqdec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | ParseMPLS =>
      {| st_op :=
          extract(HdrMPLS) ;
         st_trans := transition select (| (@EHdr header sz HdrMPLS)[23 -- 23] |) {{
            [| exact #b|1 |] ==> inl ParseUDP ;;;
            [| exact #b|0 |] ==> inl ParseMPLS ;;;
              reject
          }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition accept |}
    end.



  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct h || destruct s; cbv; Lia.lia).

End Plain.

Module Unrolled.
  Inductive state :=
  | ParseMPLS
  | ParseUDP
  | Cleanup.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS; ParseUDP; Cleanup] |}.
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
  | HdrMPLS0
  | HdrMPLS1 
  | Tmp 
  | HdrUDP .

  Scheme Equality for header.

  Definition sz (h: header) : nat :=
    match h with
    | HdrMPLS0 => 32
    | HdrMPLS1 => 32
    | Tmp => 32
    | HdrUDP => 64
    end.

  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.

  Global Instance header_finite': @Finite header _ header_eqdec.
  Proof.
    solve_finiteness.
  Defined.

  Notation EHdr' := (@EHdr header sz).

  Definition states (s: state) :=
    match s with
    | ParseMPLS =>
      {| st_op :=
          extract(HdrMPLS0) ;;
          extract(HdrMPLS1) ;
         st_trans := transition select (| (EHdr' HdrMPLS0)[23 -- 23], (EHdr' HdrMPLS1)[23 -- 23]|) {{
          [| exact (#b|1), * |] ==> inl Cleanup ;;;
          [| exact (#b|0), exact (#b|1) |] ==> inl ParseUDP ;;;
          [| exact (#b|0), exact (#b|0) |] ==> inl ParseMPLS ;;;
            reject
          }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP) ;
         st_trans := transition accept |}
    | Cleanup =>
      {| st_op := 
        extract(Tmp) ;; 
        HdrUDP <- EConcat (EHdr' HdrMPLS1) (EHdr Tmp);
        st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct h || destruct s; cbv; Lia.lia).

End Unrolled.

Module MPLSVect.
  Definition aut := Sum.sum Plain.aut Unrolled.aut.
End MPLSVect.