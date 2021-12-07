Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Notations.
Require Import Leapfrog.BisimChecker.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.


Module Sloppy.

  Inductive state :=
  | ParseEthernet
  | ParseIPv4
  | ParseIPv6
  .

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseEthernet; ParseIPv4; ParseIPv6] |}.
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
  | HdrEthernet : header 112
  | HdrIPv4 : header 128
  | HdrIPv6 : header 288
  .

  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y} :=
    match x, y with
    | HdrEthernet, HdrEthernet => left eq_refl
    | _, _ => idProp
    end.

  Definition h128_eq_dec (x y: header 128) : {x = y} + {x <> y} :=
    match x, y with
    | HdrIPv4, HdrIPv4 => left eq_refl
    | _, _ => idProp
    end.

  Definition h288_eq_dec (x y: header 288) : {x = y} + {x <> y} :=
    match x, y with
    | HdrIPv6, HdrIPv6 => left eq_refl
    | _, _ => idProp
    end.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  Proof.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec) ::
        (existT _ _ h128_eq_dec) :: (existT _ _ h288_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [288; 128; 112].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ HdrEthernet; existT _ _ HdrIPv4; existT _ _ HdrIPv6]; |}.
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
    | ParseEthernet =>
      {| st_op := extract(HdrEthernet) ;
         st_trans := transition select (| ESlice (EHdr HdrEthernet) 111 96 |) {{
           [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
            inl ParseIPv4
         }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4) ;
         st_trans := transition accept
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End Sloppy.

Module Strict.

  Inductive state :=
  | ParseEthernet
  | ParseIPv4
  | ParseIPv6
  .

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseEthernet; ParseIPv4; ParseIPv6] |}.
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
  | HdrEthernet : header 112
  | HdrIPv4 : header 128
  | HdrIPv6 : header 288
  .

  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y} :=
    match x, y with
    | HdrEthernet, HdrEthernet => left eq_refl
    | _, _ => idProp
    end.

  Definition h128_eq_dec (x y: header 128) : {x = y} + {x <> y} :=
    match x, y with
    | HdrIPv4, HdrIPv4 => left eq_refl
    | _, _ => idProp
    end.

  Definition h288_eq_dec (x y: header 288) : {x = y} + {x <> y} :=
    match x, y with
    | HdrIPv6, HdrIPv6 => left eq_refl
    | _, _ => idProp
    end.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  Proof.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h112_eq_dec) ::
        (existT _ _ h128_eq_dec) :: (existT _ _ h288_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [288; 128; 112].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ HdrEthernet; existT _ _ HdrIPv4; existT _ _ HdrIPv6]; |}.
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
    | ParseEthernet =>
      {| st_op := extract(HdrEthernet) ;
         st_trans := transition select (| ESlice (EHdr HdrEthernet) 111 96 |) {{
           [| hexact 0x86dd |] ==> inl ParseIPv6 ;;;
           [| hexact 0x8600 |] ==> inl ParseIPv4 ;;;
            reject
         }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4) ;
         st_trans := transition accept
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End Strict.

Module SloppyStrict.
  Definition aut := Sum.sum Sloppy.aut Strict.aut.
End SloppyStrict.
