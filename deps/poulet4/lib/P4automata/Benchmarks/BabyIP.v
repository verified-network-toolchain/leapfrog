Require Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.ConfRel.

Module BabyIP1.
  Inductive state :=
  | Start
  | ParseUDP
  | ParseTCP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Qed.

  Inductive header : nat -> Type :=
  | HdrIP: header 20
  | HdrUDP: header 20
  | HdrTCP: header 28.

  Global Instance header_eqdec': EquivDec.EqDec (H' header) eq.
  Proof.
    solve_eqdec'.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [20; 28].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrIP ; existT _ _ HdrUDP; existT _ _ HdrTCP ] |}.
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
    | Start =>
      {| st_op := OpExtract (existT header 20 HdrIP);
         st_trans := P4A.TSel (CExpr (ESlice (n := 20) (EHdr HdrIP) 19 16))
                              [{| sc_pat := PExact (VBits 4 (tt, false, false, false, true));
                                  sc_st := inl ParseUDP |};
                              {| sc_pat := PExact (VBits 4 (tt, false, false, false, false));
                                 sc_st := inl ParseTCP |}]
                              (inr false) |}
    | ParseUDP =>
      {| st_op := OpExtract (existT header 20 HdrUDP);
         st_trans := P4A.TGoto _ (inr true) |}
    | ParseTCP =>
      {| st_op := OpExtract (existT header 28 HdrTCP);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve All Obligations with (destruct s; cbv; Lia.lia).
End BabyIP1.

Module BabyIP2.
  Inductive state :=
  | Start
  | ParseSeq.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.

  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Qed.

  Inductive header: nat -> Type :=
  | HdrCombi: header 40
  | HdrSeq: header 8.

  Global Instance header_eqdec': EquivDec.EqDec {n & header n} eq.
  Proof.
    solve_eqdec'.
  Qed.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [40; 8].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ HdrCombi ; existT _ _ HdrSeq ] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
  Qed.
  Next Obligation.
  dependent destruction X; subst.
  - left; trivial.
  - right. left. trivial.
  Qed.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := OpExtract (existT header 40 HdrCombi);
         st_trans := P4A.TSel (CExpr (ESlice (n := 40) (EHdr HdrCombi) 19 16))
                              [{| sc_pat := PExact (VBits 4 (tt, false, false, false, true));
                                  sc_st := inr true |};
                              {| sc_pat := PExact (VBits 4 (tt, false, false, false, false));
                                 sc_st := inl ParseSeq |}]
                              (inr false) |}
    | ParseSeq =>
      {| st_op := OpExtract (existT header 8 HdrSeq);
         st_trans := P4A.TGoto _ (inr true) |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BabyIP2.

Module BabyIP.
  Definition aut := Sum.sum BabyIP1.aut BabyIP2.aut.
End BabyIP.
