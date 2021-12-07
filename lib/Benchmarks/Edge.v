Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.

Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.ConfRel.
Require Import Leapfrog.Notations.

Require Import Leapfrog.BisimChecker.
Require Import Coq.Program.Equality.

Open Scope p4a.

Module Plain.
  Inductive header: Type :=
  | HdrEth0
  | HdrEth1
  | HdrMPLS0
  | HdrMPLS1
  | HdrEoMPLS
  | HdrIPVer
  | HdrIPv4_5
  | HdrIPv4_6
  | HdrIPv4_7
  | HdrIPv4_8
  | HdrIPv6.

  Definition sz (h: header) :=
    match h with
    | HdrEth0
    | HdrEth1 => 112
    | HdrMPLS0
    | HdrMPLS1 => 32
    | HdrEoMPLS => 28
    | HdrIPVer => 4
    | HdrIPv4_5 => 152
    | HdrIPv4_6 => 184
    | HdrIPv4_7 => 216
    | HdrIPv4_8 => 248
    | HdrIPv6 => 316
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive state: Type :=
  | ParseEth0
  | ParseEth1
  | ParseMPLS0
  | ParseMPLS1
  | ParseEoMPLS
  | ParseIPVer
  | IgnoreIPVer4
  | IgnoreIPVer6
  | ParseIPv4
  | ParseIPv4_5
  | ParseIPv4_6
  | ParseIPv4_7
  | ParseIPv4_8
  | ParseIPv6.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Notation EHdr' := (@EHdr header sz).

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | ParseEth0 =>
      {| st_op := extract(HdrEth0);
        st_trans := transition select (| (EHdr' HdrEth0)[111--96] |)
                                {{[| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|0|1|1|1 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|1|0|0|0 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl IgnoreIPVer4 ;;;
                                  [| exact #b|1|0|0|0|0|1|1|0|1|1|0|1|1|1|0|1 |] ==> inl IgnoreIPVer6 ;;;
                                  accept }}
      |}
    | ParseMPLS0 =>
      {| st_op := extract(HdrMPLS0);
        st_trans := transition select (| (EHdr' HdrMPLS0)[23--23] |)
                                {{ [| hexact 0 |] ==> inl ParseMPLS1 ;;;
                                  [| hexact 1 |] ==> inl ParseIPVer ;;;
                                  reject
                                }}
      |}
    | ParseMPLS1 =>
      {| st_op := extract(HdrMPLS1);
        st_trans := transition select (| (EHdr' HdrMPLS1)[23--23] |)
                              {{ [| hexact 1 |] ==> inl ParseIPVer ;;;
                                reject
                              }}
      |}
    | ParseIPVer =>
      {| st_op := extract(HdrIPVer);
        st_trans := transition select (| EHdr' HdrIPVer |)
                                {{ [| exact #b|0|0|0|0 |] ==> inl ParseEoMPLS;;;
                                  [| exact #b|0|1|0|0 |] ==> inl ParseIPv4;;;
                                  [| exact #b|0|1|1|0 |] ==> inl ParseIPv6;;;
                                  reject
                                }}
      |}
    | IgnoreIPVer4 => {|
      st_op := extract(HdrIPVer);
      st_trans := transition (inl ParseIPv4);
    |}
    | IgnoreIPVer6 => {|
      st_op := extract(HdrIPVer);
      st_trans := transition (inl ParseIPv6);
    |}
    | ParseEoMPLS =>
      {| st_op := extract(HdrEoMPLS);
        st_trans := transition (inl ParseEth1) |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPVer);
        st_trans := transition select (| EHdr' HdrIPVer |)
                                {{  [| exact #b|0|1|0|1 |] ==> inl ParseIPv4_5;;;
                                    [| exact #b|0|1|1|0 |] ==> inl ParseIPv4_6;;;
                                    [| exact #b|0|1|1|1 |] ==> inl ParseIPv4_7;;;
                                    [| exact #b|1|0|0|0 |] ==> inl ParseIPv4_8;;;
                                  reject
                                }}

      |}
    | ParseIPv4_5 =>
      {| st_op := extract(HdrIPv4_5);
        st_trans := transition accept |}
    | ParseIPv4_6 =>
      {| st_op := extract(HdrIPv4_6);
        st_trans := transition accept |}
    | ParseIPv4_7 =>
      {| st_op := extract(HdrIPv4_7);
        st_trans := transition accept |}
    | ParseIPv4_8 =>
      {| st_op := extract(HdrIPv4_8);
        st_trans := transition accept |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6);
        st_trans := transition accept |}
    | ParseEth1 =>
      {| st_op := extract(HdrEth1);
        st_trans := transition accept |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End Plain.

Module Optimized.
Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Sum.
Require Import Leapfrog.Syntax.
Require Import Leapfrog.BisimChecker.

Require Import Leapfrog.Notations.

Open Scope p4a.

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.
Inductive state := | State_0 | State_1 | State_1_suff_0 | State_0_suff_3 | State_3_suff_1 | State_4 | State_4_trailer | State_4_skip | State_2_suff_0 | State_3 | State_3_suff_2 | State_0_suff_2 | State_2 | State_3_suff_3 | State_3_suff_0 | State_0_suff_1.
Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Instance state_finite: @Finite state _ state_eq_dec.
Proof.
  solve_finiteness.
Defined.

Inductive header :=
| buf_320
| buf_128
| buf_64
| buf_112
| buf_16
| buf_32
| buf_304
| buf_240
| buf_144
| buf_176
| buf_208.

Definition sz (h: header) : nat :=
  match h with
  | buf_320 => 320
  | buf_128 => 128
  | buf_64 => 64
  | buf_112 => 112
  | buf_16 => 16
  | buf_32 => 32
  | buf_304 => 304
  | buf_240 => 240
  | buf_144 => 144
  | buf_176 => 176
  | buf_208 => 208
  end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Notation EHdr' := (@EHdr header sz).

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | State_0 => {|
      st_op := extract(buf_112);
      st_trans := transition select (| (EHdr' buf_112)[111 -- 96] |) {{
        [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl State_3 ;;;
        [| exact #b|1|0|0|0|0|1|1|0|1|1|0|1|1|1|0|1 |] ==> inl State_0_suff_1 ;;;
        [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|0|1|1|1 |] ==> inl State_0_suff_2 ;;;
        [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|1|0|0|0 |] ==> inl State_0_suff_3 ;;;
        accept
      }}
    |}
    | State_0_suff_1 => {|
      st_op := extract(buf_320);
      st_trans := transition accept;
    |}
    | State_0_suff_2 => {|
      st_op := extract(buf_16);
      st_trans := transition inl State_4;
    |}
    | State_0_suff_3 => {|
      st_op := extract(buf_16);
      st_trans := transition inl State_4;
    |}
    | State_1 => {|
      st_op := extract(buf_16);
      st_trans := transition inl State_1_suff_0;

    |}
    | State_1_suff_0 => {|
      st_op := extract(buf_128);
      st_trans := transition accept;
    |}
    | State_2 => {|
      st_op := extract(buf_16);
      st_trans := transition inl State_2_suff_0;
    |}
    | State_2_suff_0 => {|
      st_op := extract(buf_304);
      st_trans := transition accept;
    |}
    | State_3 => {|
      st_op := extract(buf_16);
      st_trans := transition select (| (EHdr' buf_16)[7--4]|) {{
        [| exact #b|0|1|0|1 |] ==> inl State_3_suff_0 ;;;
        [| exact #b|0|1|1|0 |] ==> inl State_3_suff_1 ;;;
        [| exact #b|0|1|1|1 |] ==> inl State_3_suff_2 ;;;
        [| exact #b|1|0|0|0 |] ==> inl State_3_suff_3 ;;;
        reject
      }}
    |}
    | State_3_suff_0 => {|
      st_op := extract(buf_144);
      st_trans := transition accept;
    |}
    | State_3_suff_1 => {|
      st_op := extract(buf_176);
      st_trans := transition accept;
    |}
    | State_3_suff_2 => {|
      st_op := extract(buf_208);
      st_trans := transition accept;
    |}
    | State_3_suff_3 => {|
      st_op := extract(buf_240);
      st_trans := transition accept;
    |}

    | State_4 => {|
      st_op := extract(buf_16);
      st_trans := transition select (| (EHdr' buf_16)[7 -- 7] |) {{
        [| exact #b|0 |] ==> inl State_4_skip ;;;
        [| exact #b|1 |] ==> inl State_4_trailer ;;;
        reject
      }}
    |}

    | State_4_skip => {|
      st_op := extract(buf_32);
      st_trans := transition select (| (EHdr' buf_32)[23 -- 23] |) {{
        [| exact #b|1 |] ==> inl State_4_trailer ;;;
        reject
      }}
    |}

    | State_4_trailer => {|
      st_op := extract(buf_16);
      st_trans := transition select (| (EHdr' buf_16)[3 -- 0], (EHdr' buf_16)[7--4] |) {{
        [| exact #b|0|0|0|0, * |] ==> inl State_1_suff_0 (* State_1 but with 16 bits rem *) ;;;
        [| exact #b|0|1|1|0, * |] ==> inl State_2_suff_0 (* State_2 but with 16 bits rem *) ;;;
        [| exact #b|0|1|0|0, exact #b|0|1|0|1 |] ==> inl State_3_suff_0 (* State_3 but with 16 bits rem *) ;;;
        [| exact #b|0|1|0|0, exact #b|0|1|1|0 |] ==> inl State_3_suff_1 (* State_3 but with 16 bits rem *) ;;;
        [| exact #b|0|1|0|0, exact #b|0|1|1|1 |] ==> inl State_3_suff_2 (* State_3 but with 16 bits rem *) ;;;
        [| exact #b|0|1|0|0, exact #b|1|0|0|0 |] ==> inl State_3_suff_3 (* State_3 but with 16 bits rem *) ;;;
        reject
      }}
    |}
  end.
  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End Optimized.
