Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.

Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Notations.

Open Scope p4a.

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

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrIP HdrIP := left eq_refl ;
    header_eqdec_ _ HdrTCP HdrTCP := left eq_refl ;
    header_eqdec_ _ HdrUDP HdrUDP := left eq_refl ;
    header_eqdec_ _ _ _ := ltac:(right; congruence) ;
  }.
  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

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
      {| st_op := extract(HdrIP);
         st_trans := transition select (| (EHdr HdrIP)[19 -- 16] |) {{
          [| exact #b|0|0|0|1 |] ==> inl ParseUDP ;;;
          [| exact #b|0|0|0|0 |] ==> inl ParseTCP ;;;
          reject
         }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
         st_trans := transition accept |}
    | ParseTCP =>
      {| st_op := extract(HdrTCP);
         st_trans := transition accept |}
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

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ HdrCombi HdrCombi := left eq_refl ;
    header_eqdec_ _ HdrSeq HdrSeq := left eq_refl ;
  }.
  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

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
      {| st_op := extract(HdrCombi);
         st_trans := transition select (| (EHdr HdrCombi)[19 -- 16] |) {{
          [| exact #b|0|0|0|1 |] ==> accept ;;;
          [| exact #b|0|0|0|0 |] ==> inl ParseSeq ;;;
            reject
        }}
      |}
    | ParseSeq =>
      {| st_op := extract(HdrSeq);
         st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state _ :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End BabyIP2.

Module BabyIP.
  Definition aut := Sum.sum BabyIP1.aut BabyIP2.aut.
End BabyIP.
