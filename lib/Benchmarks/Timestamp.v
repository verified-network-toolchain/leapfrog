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

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module TimestampRefKeepSingle.
  Inductive state :=
  | Start
  | ParseValue1
  | ParseValue2
  | ParseValue3
  | ParseValue4
  | ParseValue5
  | ParseValue6.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Typ
  | Len
  | Value
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): N :=
    match h with
    | Typ => 8
    | Len => 8
    | Value => 48
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    end.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Start =>
      {| st_op :=
          extract(Typ) ;;
          extract(Len) ;
        st_trans := transition select (| EHdr Len |) {{
          [| exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
          [| exact #b|0|0|0|0|0|0|0|1 |] ==> inl ParseValue1 ;;;
          [| exact #b|0|0|0|0|0|0|1|0 |] ==> inl ParseValue2 ;;;
          [| exact #b|0|0|0|0|0|0|1|1 |] ==> inl ParseValue3 ;;;
          [| exact #b|0|0|0|0|0|1|0|0 |] ==> inl ParseValue4 ;;;
          [| exact #b|0|0|0|0|0|1|0|1 |] ==> inl ParseValue5 ;;;
          [| exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseValue6 ;;;
            reject
        }}
      |}
    | ParseValue1 =>
      {| st_op :=
          extract(Scratch8) ;;
          Value <- EConcat (m := 40) (EHdr Scratch8) ((@EHdr _ sz Value)[48--8])  ;
        st_trans := transition accept
      |}
    | ParseValue2 =>
      {| st_op :=
          extract(Scratch16) ;;
          Value <- EConcat (m := 32) (EHdr Scratch16) ((@EHdr _ sz Value)[48--16])  ;
        st_trans := transition accept
      |}
    | ParseValue3 =>
      {| st_op :=
          extract(Scratch24) ;;
          Value <- EConcat (m := 24) (EHdr Scratch24) ((@EHdr _ sz Value)[48--24])  ;
        st_trans := transition accept
      |}
    | ParseValue4 =>
      {| st_op :=
          extract(Scratch32) ;;
          Value <- EConcat (m := 16) (EHdr Scratch32) ((@EHdr _ sz Value)[48--32])  ;
        st_trans := transition accept
      |}
    | ParseValue5 =>
      {| st_op :=
          extract(Scratch40) ;;
          Value <- EConcat (m := 8) (EHdr Scratch40) ((@EHdr _ sz Value)[48--40])  ;
        st_trans := transition accept
      |}
    | ParseValue6 =>
      {| st_op := extract(Value) ;
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampRefKeepSingle.

Module TimestampRefZeroSingle.
  Inductive state :=
  | Start
  | ParseValue1
  | ParseValue2
  | ParseValue3
  | ParseValue4
  | ParseValue5
  | ParseValue6.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Typ
  | Len
  | Value
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): N :=
    match h with
    | Typ => 8
    | Len => 8
    | Value => 48
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    end.

  Definition states (s: state) :=
    match s with
    | Start =>
      {| st_op :=
          extract(Typ) ;;
          extract(Len) ;
        st_trans := transition select (| EHdr Len |) {{
          [| exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
          [| exact #b|0|0|0|0|0|0|0|1 |] ==> inl ParseValue1 ;;;
          [| exact #b|0|0|0|0|0|0|1|0 |] ==> inl ParseValue2 ;;;
          [| exact #b|0|0|0|0|0|0|1|1 |] ==> inl ParseValue3 ;;;
          [| exact #b|0|0|0|0|0|1|0|0 |] ==> inl ParseValue4 ;;;
          [| exact #b|0|0|0|0|0|1|0|1 |] ==> inl ParseValue5 ;;;
          [| exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseValue6 ;;;
            reject
        }}
      |}
    | ParseValue1 =>
      {| st_op :=
          extract(Scratch8) ;;
          Value <- EConcat (n := 8) (EHdr (Hdr_sz := sz) Scratch8) (ELit _ (Ntuple.n_tuple_repeat 40 false))  ;
        st_trans := transition accept
      |}
    | ParseValue2 =>
      {| st_op :=
          extract(Scratch16) ;;
          Value <- EConcat (n := 16) (EHdr (Hdr_sz := sz) Scratch16) (ELit _ (Ntuple.n_tuple_repeat 32 false))  ;
        st_trans := transition accept
      |}
    | ParseValue3 =>
      {| st_op :=
          extract(Scratch24) ;;
          Value <- EConcat (n := 24) (EHdr (Hdr_sz := sz) Scratch24) (ELit _ (Ntuple.n_tuple_repeat 24 false))  ;
        st_trans := transition accept
      |}
    | ParseValue4 =>
      {| st_op :=
          extract(Scratch32) ;;
          Value <- EConcat (n := 32) (EHdr (Hdr_sz := sz) Scratch32) (ELit _ (Ntuple.n_tuple_repeat 16 false))  ;
        st_trans := transition accept
      |}
    | ParseValue5 =>
      {| st_op :=
          extract(Scratch40) ;;
          Value <- EConcat (n := 40) (EHdr (Hdr_sz := sz) Scratch40) (ELit _ (Ntuple.n_tuple_repeat 8 false))  ;
        st_trans := transition accept
      |}
    | ParseValue6 =>
      {| st_op := extract(Value) ;
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampRefZeroSingle.

Module TimestampSpecSingle.
  Inductive state :=
  | Start
  | ParseValue1
  | ParseValue2
  | ParseValue3
  | ParseValue4
  | ParseValue5
  | ParseValue6
  | ParseTimestamp.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Typ
  | Len
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | Scratch48
  | Pointer
  | Overflow
  | Flag
  | Timestamp.

  Definition sz (h: header): N :=
    match h with
    | Typ => 8
    | Len => 8
    | Scratch8 => 8
    | Scratch16 => 16
    | Scratch24 => 24
    | Scratch32 => 32
    | Scratch40 => 40
    | Scratch48 => 48
    | Pointer => 8
    | Overflow => 4
    | Flag => 4
    | Timestamp => 32
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Start =>
      {| st_op :=
          extract(Typ) ;;
          extract(Len) ;
        st_trans := transition select (| EHdr Typ, EHdr Len |) {{
          [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseTimestamp ;;;
          [| *, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
          [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl ParseValue1 ;;;
          [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl ParseValue2 ;;;
          [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl ParseValue3 ;;;
          [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl ParseValue4 ;;;
          [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl ParseValue5 ;;;
          [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl ParseValue6 ;;;
            reject
        }}
      |}
    | ParseTimestamp =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition accept (* TODO: validate pointer and flag? *)
      |}
    | ParseValue1 =>
      {| st_op :=
          extract(Scratch8) ;
        st_trans := transition accept
      |}
    | ParseValue2 =>
      {| st_op :=
          extract(Scratch16) ;
        st_trans := transition accept
      |}
    | ParseValue3 =>
      {| st_op :=
          extract(Scratch24) ;
        st_trans := transition accept
      |}
    | ParseValue4 =>
      {| st_op :=
          extract(Scratch32) ;
        st_trans := transition accept
      |}
    | ParseValue5 =>
      {| st_op :=
          extract(Scratch40) ;
        st_trans := transition accept
      |}
    | ParseValue6 =>
      {| st_op := extract(Scratch48) ;
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampSpecSingle.


Module TimestampRefSmall.
  Inductive state :=
  | Start
  | Parse1
  | Parse2
  | Parse3.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Len
  | Pref1
  | Pref2
  | Timestamps.

  Definition sz (h: header): N :=
    match h with
    | Len => 2
    | Pref1 => 8
    | Pref2 => 16
    | Timestamps => 24
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
      {| st_op :=
          extract(Len) ;
         st_trans := transition select (| EHdr Len |) {{
           [| exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|1 |] ==> inl Parse1 ;;;
           [| exact #b|1|0 |] ==> inl Parse2 ;;;
           [| exact #b|1|1 |] ==> inl Parse3 ;;;
            reject
         }}
      |}
    | Parse1 =>
      {| st_op :=
          extract(Pref1) ;;
          Timestamps <- EConcat (m := 16) (EHdr Pref1) ((EHdr (Hdr_sz := sz) Timestamps)[24--8])  ;
         st_trans := transition accept
      |}
    | Parse2 =>
      {| st_op :=
          extract(Pref2) ;;
          Timestamps <- EConcat (m := 8) (EHdr Pref2) ((EHdr (Hdr_sz := sz) Timestamps)[24--16]) ;
         st_trans := transition accept
      |}
    | Parse3 =>
      {| st_op := extract(Timestamps) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampRefSmall.

Module TimestampSpecSmall.
  Inductive state :=
  | Start
  | Parse1
  | Parse2
  | Parse3.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Len
  | T1
  | T2
  | T3.

  Definition sz (h: header): N :=
    match h with
    | Len => 2
    | T1 | T2 | T3 => 8
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Start =>
      {| st_op :=
          extract(Len) ;
         st_trans := transition select (| EHdr Len |) {{
           [| exact #b|0|0 |] ==> accept ;;;
           [| exact #b|0|1 |] ==> inl Parse1 ;;;
           [| exact #b|1|0 |] ==> inl Parse2 ;;;
           [| exact #b|1|1 |] ==> inl Parse3 ;;;
            reject
         }}
      |}
    | Parse1 =>
      {| st_op :=
          extract(T1) ;
         st_trans := transition accept
      |}
    | Parse2 =>
      {| st_op :=
          extract(T1) ;;
          extract(T2) ;
         st_trans := transition accept
      |}
    | Parse3 =>
      {| st_op :=
          extract(T1) ;;
          extract(T2) ;;
          extract(T3) ;
         st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampSpecSmall.

(* parse 2 options of between 0-6 bytes, and if a timestamp option is present, parse it into a timestamp structure *)
Module TimestampSpec2.
  Inductive state :=
  | Parse0
  | Parse1

  | Parse0S
  | Parse1S

  | Parse01
  | Parse11

  | Parse02
  | Parse12

  | Parse03
  | Parse13

  | Parse04
  | Parse14

  | Parse05
  | Parse15

  | Parse06
  | Parse16.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1
  | Pointer
  | Overflow
  | Flag
  | Timestamp.

  Definition sz (h: header): N :=
    match h with
    | Scratch8  => 8
    | Scratch16  => 16
    | Scratch24  => 24
    | Scratch32  => 32
    | Scratch40  => 40
    | T0  => 8
    | L0  => 8
    | V0  => 48
    | T1  => 8
    | L1  => 8
    | V1  => 48
    | Pointer  => 8
    | Overflow => 4
    | Flag => 4
    | Timestamp => 32
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) T0, EHdr (Hdr_sz := sz) L0 |) {{
           [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse0S;;;
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op :=
          extract(Scratch8) ;;
          V0 <- EConcat (m := 40) (EHdr (Hdr_sz := sz) Scratch8) ((EHdr (Hdr_sz := sz) V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr (Hdr_sz := sz) Scratch16) ((EHdr (Hdr_sz := sz) V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr (Hdr_sz := sz) Scratch24) ((EHdr (Hdr_sz := sz) V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr (Hdr_sz := sz) Scratch32) ((EHdr (Hdr_sz := sz) V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr (Hdr_sz := sz) Scratch40) ((EHdr (Hdr_sz := sz) V0)[48--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op :=
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse0S =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition inl Parse1 ;
      |}

    | Parse1 =>
      {| st_op :=
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) T1, EHdr (Hdr_sz := sz) L1 |) {{
           [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse1S;;;
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr (Hdr_sz := sz) Scratch8) ((EHdr (Hdr_sz := sz) V1)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr (Hdr_sz := sz) Scratch16) ((EHdr (Hdr_sz := sz) V1)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr (Hdr_sz := sz) Scratch24) ((EHdr (Hdr_sz := sz) V1)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr (Hdr_sz := sz) Scratch32) ((EHdr (Hdr_sz := sz) V1)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr (Hdr_sz := sz) Scratch40) ((EHdr (Hdr_sz := sz) V1)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse16 =>
      {| st_op :=
          extract(V1) ;
         st_trans := transition accept;
      |}
    | Parse1S =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition accept ;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampSpec2.


(* parse 3 options of between 0-6 bytes, and if a timestamp option is present, parse it into a timestamp structure *)
Module TimestampSpec3.
  Inductive state :=
  | Parse0
  | Parse1
  | Parse2

  | Parse0S
  | Parse1S
  | Parse2S

  | Parse01
  | Parse11
  | Parse21

  | Parse02
  | Parse12
  | Parse22

  | Parse03
  | Parse13
  | Parse23

  | Parse04
  | Parse14
  | Parse24

  | Parse05
  | Parse15
  | Parse25

  | Parse06
  | Parse16
  | Parse26.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | Scratch8
  | Scratch16
  | Scratch24
  | Scratch32
  | Scratch40
  | T0
  | L0
  | V0
  | T1
  | L1
  | V1
  | T2
  | L2
  | V2
  | Pointer
  | Overflow
  | Flag
  | Timestamp.

  Definition sz (h: header): N :=
    match h with
    | Scratch8  => 8
    | Scratch16  => 16
    | Scratch24  => 24
    | Scratch32  => 32
    | Scratch40  => 40
    | T0  => 8
    | L0  => 8
    | V0  => 48
    | T1  => 8
    | L1  => 8
    | V1  => 48
    | T2  => 8
    | L2  => 8
    | V2  => 48
    | Pointer  => 8
    | Overflow => 4
    | Flag => 4
    | Timestamp => 32
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : Syntax.state state sz :=
    match s with
    | Parse0 =>
      {| st_op :=
          extract(T0) ;;
          extract(L0) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) T0, EHdr (Hdr_sz := sz) L0 |) {{
           [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse0S;;;
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse01 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse02 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse03 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse04 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse05 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse06 ;;;
            reject
         }}
      |}
    | Parse01 =>
      {| st_op :=
          extract(Scratch8) ;;
          V0 <- EConcat (m := 40) (EHdr (Hdr_sz := sz) Scratch8) ((EHdr (Hdr_sz := sz) V0)[48--8]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse02 =>
      {| st_op :=
          extract(Scratch16) ;;
          V0 <- EConcat (m := 32) (EHdr (Hdr_sz := sz) Scratch16) ((EHdr (Hdr_sz := sz) V0)[48--16]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse03 =>
      {| st_op :=
          extract(Scratch24) ;;
          V0 <- EConcat (m := 24) (EHdr (Hdr_sz := sz) Scratch24) ((EHdr (Hdr_sz := sz) V0)[48--24]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse04 =>
      {| st_op :=
          extract(Scratch32) ;;
          V0 <- EConcat (m := 16) (EHdr (Hdr_sz := sz) Scratch32) ((EHdr (Hdr_sz := sz) V0)[48--32]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse05 =>
      {| st_op :=
          extract(Scratch40) ;;
          V0 <- EConcat (m := 8) (EHdr (Hdr_sz := sz) Scratch40) ((EHdr (Hdr_sz := sz) V0)[48--40]) ;
         st_trans := transition inl Parse1;
      |}
    | Parse06 =>
      {| st_op :=
          extract(V0) ;
         st_trans := transition inl Parse1;
      |}

    | Parse0S =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition inl Parse1 ;
      |}

    | Parse1 =>
      {| st_op :=
          extract(T1) ;;
          extract(L1) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) T1, EHdr (Hdr_sz := sz) L1 |) {{
           [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse1S;;;
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse11 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse12 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse13 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse14 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse15 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse16 ;;;
            reject
         }}
      |}
    | Parse11 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr (Hdr_sz := sz) Scratch8) ((EHdr (Hdr_sz := sz) V1)[48--8]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse12 =>
      {| st_op :=
          extract(Scratch16) ;;
          V1 <- EConcat (m := 32) (EHdr (Hdr_sz := sz) Scratch16) ((EHdr (Hdr_sz := sz) V1)[48--16]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse13 =>
      {| st_op :=
          extract(Scratch24) ;;
          V1 <- EConcat (m := 24) (EHdr (Hdr_sz := sz) Scratch24) ((EHdr (Hdr_sz := sz) V1)[48--24]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse14 =>
      {| st_op :=
          extract(Scratch32) ;;
          V1 <- EConcat (m := 16) (EHdr (Hdr_sz := sz) Scratch32) ((EHdr (Hdr_sz := sz) V1)[48--32]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse15 =>
      {| st_op :=
          extract(Scratch40) ;;
          V1 <- EConcat (m := 8) (EHdr (Hdr_sz := sz) Scratch40) ((EHdr (Hdr_sz := sz) V1)[48--40]) ;
         st_trans := transition inl Parse2;
      |}
    | Parse16 =>
      {| st_op :=
          extract(V1) ;
         st_trans := transition inl Parse2;
      |}
    | Parse1S =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition inl Parse2 ;
      |}

    | Parse2 =>
      {| st_op :=
          extract(T2) ;;
          extract(L2) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) T2, EHdr (Hdr_sz := sz) L2 |) {{
           [| exact #b|0|1|0|0|0|1|0|0, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse2S;;;
           [| exact #b|0|0|0|0|0|0|0|0, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| exact #b|0|0|0|0|0|0|0|1, exact #b|0|0|0|0|0|0|0|0 |] ==> accept ;;;
           [| *, exact #b|0|0|0|0|0|0|0|1 |] ==> inl Parse21 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|0 |] ==> inl Parse22 ;;;
           [| *, exact #b|0|0|0|0|0|0|1|1 |] ==> inl Parse23 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|0 |] ==> inl Parse24 ;;;
           [| *, exact #b|0|0|0|0|0|1|0|1 |] ==> inl Parse25 ;;;
           [| *, exact #b|0|0|0|0|0|1|1|0 |] ==> inl Parse26 ;;;
            reject
         }}
      |}
    | Parse21 =>
      {| st_op :=
          extract(Scratch8) ;;
          V1 <- EConcat (m := 40) (EHdr (Hdr_sz := sz) Scratch8) ((EHdr (Hdr_sz := sz) V2)[48--8]) ;
         st_trans := transition accept;
      |}
    | Parse22 =>
      {| st_op :=
          extract(Scratch16) ;;
          V2 <- EConcat (m := 32) (EHdr (Hdr_sz := sz) Scratch16) ((EHdr (Hdr_sz := sz) V2)[48--16]) ;
         st_trans := transition accept;
      |}
    | Parse23 =>
      {| st_op :=
          extract(Scratch24) ;;
          V2 <- EConcat (m := 24) (EHdr (Hdr_sz := sz) Scratch24) ((EHdr (Hdr_sz := sz) V2)[48--24]) ;
         st_trans := transition accept;
      |}
    | Parse24 =>
      {| st_op :=
          extract(Scratch32) ;;
          V2 <- EConcat (m := 16) (EHdr (Hdr_sz := sz) Scratch32) ((EHdr (Hdr_sz := sz) V2)[48--32]) ;
         st_trans := transition accept;
      |}
    | Parse25 =>
      {| st_op :=
          extract(Scratch40) ;;
          V2 <- EConcat (m := 8) (EHdr (Hdr_sz := sz) Scratch40) ((EHdr (Hdr_sz := sz) V2)[48--40]) ;
         st_trans := transition accept;
      |}
    | Parse26 =>
      {| st_op :=
          extract(V2) ;
         st_trans := transition accept;
      |}
    | Parse2S =>
      {| st_op :=
          extract(Pointer) ;;
          extract(Overflow) ;;
          extract(Flag) ;;
          extract(Timestamp) ;
        st_trans := transition accept ;
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).


End TimestampSpec3.

