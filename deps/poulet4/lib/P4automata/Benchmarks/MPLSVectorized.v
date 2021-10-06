Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.

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

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrMPLS0 HdrMPLS0 := left eq_refl ;
    header_eqdec_ _ HdrMPLS1 HdrMPLS1 := left eq_refl ;
    header_eqdec_ _ HdrUDP HdrUDP := left eq_refl ;
    header_eqdec_ _ _ _ := ltac:(right; congruence) ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32; 32; 32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
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
      {| st_op := OpSeq
        (OpAsgn HdrMPLS1 (EHdr HdrMPLS0))
        (OpExtract (existT _ _ HdrMPLS0));
         st_trans := TSel (CExpr (ESlice (EHdr HdrMPLS0) 24 24))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits 1 (tt, false));
                                 sc_st := inl ParseMPLS |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract (existT _ _ HdrUDP);
         st_trans := TGoto _ (inr true) |}
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

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrMPLS0 HdrMPLS0 := left eq_refl ;
    header_eqdec_ _ HdrMPLS1 HdrMPLS1 := left eq_refl ;
    header_eqdec_ _ HdrUDP HdrUDP := left eq_refl ;
    header_eqdec_ _ _ _ := ltac:(right; congruence) ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32; 32; 32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
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
      {| st_op := OpSeq
        (OpAsgn HdrMPLS1 (EHdr HdrMPLS0))
        (OpExtract (existT _ _ HdrMPLS0));
         st_trans := TSel (CExpr (ESlice (EHdr HdrMPLS0) 24 24))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits 1 (tt, false));
                                 sc_st := inl ParseMPLS1 |}]
                              (inr false) |}
    | ParseMPLS1 =>
      {| st_op := OpSeq
        (OpAsgn HdrMPLS1 (EHdr HdrMPLS0))
        (OpExtract (existT _ _ HdrMPLS0));
          st_trans := TSel (CExpr (ESlice (EHdr HdrMPLS0) 24 24))
                              [{| sc_pat := PExact (VBits 1 (tt, true));
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits 1 (tt, false));
                                  sc_st := inl ParseMPLS0 |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract (existT _ _ HdrUDP);
         st_trans := TGoto _ (inr true) |}
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

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrMPLS0 HdrMPLS0 := left eq_refl ;
    header_eqdec_ _ HdrMPLS1 HdrMPLS1 := left eq_refl ;
    header_eqdec_ _ HdrUDP HdrUDP := left eq_refl ;
    header_eqdec_ _ _ _ := ltac:(right; congruence) ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [32; 32; 32].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrMPLS0 ; existT _ _ HdrMPLS1; existT _ _ HdrUDP ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
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
      {| st_op := OpSeq 
          (OpExtract (existT _ _ HdrMPLS1))
          (OpSeq 
            (OpExtract (existT _ _ HdrMPLS0))
            (OpAsgn HdrUDP (EHdr HdrMPLS0))
          );
         st_trans := TSel (CPair 
            (CExpr (ESlice (n := 32) (EHdr HdrMPLS1) 24 24))
            (CExpr (ESlice (n := 32) (EHdr HdrMPLS0) 24 24)))
            [{| sc_pat := PPair (PExact (VBits 1 (tt, true))) (PAny 1);
                sc_st := inr true |};
             {| sc_pat := PPair (PExact (VBits 1 (tt, false))) (PExact (VBits 1 (tt, true)));
                sc_st := inl ParseUDP |};
              {| sc_pat := PPair (PExact (VBits 1 (tt, false))) (PExact (VBits 1 (tt, false)));
                sc_st := inl ParseMPLS |}]
            (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract (existT _ _ HdrUDP);
         st_trans := TGoto _ (inr true) |}
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
