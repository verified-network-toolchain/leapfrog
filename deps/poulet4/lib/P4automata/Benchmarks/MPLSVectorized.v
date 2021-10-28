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

Module MPLSPlain.
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

  Inductive header : nat -> Type :=
  | HdrMPLS0 : header 32
  | HdrMPLS1 : header 32
  | HdrUDP : header 32.

  Derive Signature for header.

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrMPLS0 =>
      match y with
      | HdrMPLS0 => left eq_refl
      | HdrMPLS1 => right _
      | HdrUDP => right _
      end
    | HdrMPLS1 =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => left eq_refl
      | HdrUDP => right _
      end
    | HdrUDP =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => right _
      | HdrUDP => left eq_refl
      end
    end
  );
  intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 32 h32_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    solve_header_finite.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) :=
    match s with
    | ParseMPLS =>
      {| st_op :=
          HdrMPLS1 <- EHdr HdrMPLS0 ;;
          extract(HdrMPLS0) ;
         st_trans := transition select (| (EHdr HdrMPLS0)[24 -- 24] |) {{
            [| exact #b|1 |] ==> inl ParseUDP ;;;
            [| exact #b|0 |] ==> inl ParseMPLS ;;;
              reject
          }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition accept |}
    end.



  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSPlain.

Module MPLSUnroll.
  Inductive state :=
  | ParseMPLS0
  | ParseMPLS1
  | ParseUDP.
  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseMPLS0; ParseMPLS1; ParseUDP] |}.
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

  Inductive header : nat -> Type :=
  | HdrMPLS0 : header 32
  | HdrMPLS1 : header 32
  | HdrUDP : header 32.

  Derive Signature for header.

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrMPLS0 =>
      match y with
      | HdrMPLS0 => left eq_refl
      | HdrMPLS1 => right _
      | HdrUDP => right _
      end
    | HdrMPLS1 =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => left eq_refl
      | HdrUDP => right _
      end
    | HdrUDP =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => right _
      | HdrUDP => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 32 h32_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    solve_header_finite.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) :=
    match s with
    | ParseMPLS0 =>
      {| st_op :=
          HdrMPLS1 <- EHdr HdrMPLS0 ;;
          extract(HdrMPLS0);
         st_trans := transition select (| (EHdr HdrMPLS0)[24 -- 24] |) {{
          [| exact (#b|1) |] ==> inl ParseUDP ;;;
          [| exact (#b|0) |] ==> inl ParseMPLS1 ;;;
            reject
         }}
      |}
    | ParseMPLS1 =>
      {| st_op :=
          HdrMPLS1 <- EHdr HdrMPLS0 ;;
          extract(HdrMPLS0) ;
         st_trans := transition select (| (EHdr HdrMPLS0)[24 -- 24] |) {{
          [| exact (#b|1) |] ==> inl ParseUDP ;;;
          [| exact (#b|0) |] ==> inl ParseMPLS0 ;;;
            reject
         }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSUnroll.

Module MPLSInline.
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

  Inductive header : nat -> Type :=
  | HdrMPLS0 : header 32
  | HdrMPLS1 : header 32
  | HdrUDP : header 32.

  Derive Signature for header.

  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrMPLS0 =>
      match y with
      | HdrMPLS0 => left eq_refl
      | HdrMPLS1 => right _
      | HdrUDP => right _
      end
    | HdrMPLS1 =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => left eq_refl
      | HdrUDP => right _
      end
    | HdrUDP =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => right _
      | HdrUDP => left eq_refl
      end
    end
  ); intros H; inversion H.
  Defined.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 32 h32_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    solve_header_finite.
  Qed.
  Next Obligation.
  dependent destruction X; subst;
  repeat (
    match goal with
    | |- ?L \/ ?R => (now left; trivial) || right
    end
  ).
  Qed.

  Definition states (s: state) :=
    match s with
    | ParseMPLS =>
      {| st_op :=
          extract(HdrMPLS1) ;;
          extract(HdrMPLS0) ;;
          HdrUDP <- EHdr HdrMPLS0 ;
         st_trans := transition select (| (EHdr HdrMPLS1)[24 -- 24], (EHdr HdrMPLS0)[24 -- 24]|) {{
          [| exact (#b|1), * |] ==> accept ;;;
          [| exact (#b|0), exact (#b|1) |] ==> inl ParseUDP ;;;
          [| exact (#b|0), exact (#b|0) |] ==> inl ParseMPLS ;;;
            reject
          }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP) ;
         st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End MPLSInline.

Module MPLSVect.
  Definition aut := Sum.sum MPLSPlain.aut MPLSUnroll.aut.
End MPLSVect.

Module MPLSVectUnroll.
  Definition aut := Sum.sum MPLSPlain.aut MPLSInline.aut.
End MPLSVectUnroll.

Module MPLSUnrollInline.
  Definition aut := Sum.sum MPLSUnroll.aut MPLSInline.aut.
End MPLSUnrollInline.
