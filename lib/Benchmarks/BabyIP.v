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
  Inductive state : Type :=
  | Start
  | ParseUDP
  | ParseTCP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | HdrIP
  | HdrUDP
  | HdrTCP.

  Definition sz (h: header) : nat :=
    match h with
    | HdrIP => 20
    | HdrUDP => 20
    | HdrTCP => 28
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := extract(HdrIP);
         st_trans := transition select (| (@EHdr header sz HdrIP)[19 -- 16] |) {{
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
  Solve All Obligations with (destruct h || destruct s; cbv; Lia.lia).
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
  Defined.

  Inductive header :=
  | HdrCombi: header
  | HdrSeq: header.
  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header) : nat :=
    match h with
    | HdrCombi => 40
    | HdrSeq => 8
    end.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op := extract(HdrCombi);
         st_trans := transition select (| (EHdr (Hdr_sz := sz) HdrCombi)[19 -- 16] |) {{
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
  Solve Obligations with (destruct h || destruct s; cbv; Lia.lia).
End BabyIP2.

Module BabyIP.
  Definition aut := Sum.sum BabyIP1.aut BabyIP2.aut.
End BabyIP.
