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

Module TLVRefSmall.
  Inductive state :=
  | Parse1
  | Parse2
  | Parse3
  | Parse11
  | Parse21
  | Parse31
  | Parse12
  | Parse22
  | Parse32
  | Parse13
  | Parse23
  | Parse33.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | T1
  | L1
  | V1
  | T2
  | L2
  | V2
  | T3
  | L3
  | V3.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | Scratch8 => 8
    | Scratch16 => 16
    | T1 | T2 | T3 => 6
    | L1 | L2 | L3 => 2
    | V1 | V2 | V3 => 24
    end.

  Definition states (s: state) :=
    match s with
    | Parse1 =>
      {| st_op :=
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr T1, EHdr L1 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse13 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr (Hdr_sz := sz) V1)[24--8]);
         st_trans := transition (inl Parse2)
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr (Hdr_sz := sz) V1)[24--16]);
         st_trans := transition (inl Parse2)
      |}
    | Parse13 =>
      {| st_op := extract(V1) ;
         st_trans := transition (inl Parse2)
      |}

    | Parse2 =>
      {| st_op :=
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr T2, EHdr L2 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse23 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr (Hdr_sz := sz) V2)[24--8]);
         st_trans := transition (inl Parse3)
      |}
    | Parse22 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr (Hdr_sz := sz) V2)[24--16]);
         st_trans := transition (inl Parse3)
      |}
    | Parse23 =>
      {| st_op := extract(V2) ;
         st_trans := transition (inl Parse3)
      |}

    | Parse3 =>
      {| st_op :=
          extract(T3) ;;
          extract(L3) ;
         st_trans := transition select (| EHdr T3, EHdr L3 |) {{
           [| exact #b|0|0|0|0|0|0, exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|1, exact #b|0|0 |] ==> accept ;;;
           [| *, exact #b|0|1 |] ==> inl Parse31 ;;;
           [| *, exact #b|1|0 |] ==> inl Parse32 ;;;
           [| *, exact #b|1|1 |] ==> inl Parse33 ;;;
            reject
         }}
      |}
    | Parse31 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 16) (EHdr Scratch8) ((EHdr (Hdr_sz := sz) V3)[24--8]);
         st_trans := transition accept
      |}
    | Parse32 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 8) (EHdr Scratch16) ((EHdr (Hdr_sz := sz) V3)[24--16]);
         st_trans := transition accept
      |}
    | Parse33 =>
      {| st_op := extract(V2) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End TLVRefSmall.

