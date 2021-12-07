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
  Inductive header :=
  | HdrEth
  | HdrMPLS
  | HdrIPVer
  | HdrIHL
  | HdrIPv4_5
  | HdrIPv4_6
  | HdrIPv4_7
  | HdrIPv4_8
  | HdrIPv6.

  Definition sz (h: header) :=
    match h with
    | HdrEth => 112
    | HdrMPLS => 32
    | HdrIPVer => 4
    | HdrIHL => 4
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
  | ParseEth
  | ParseEthv4
  | ParseEthv6
  | ParseMPLS
  | ParseIPVer
  | ParseIPv4_5
  | ParseIPv4_6
  | ParseIPv4_7
  | ParseIPv4_8
  | ParseIPv4
  | ParseIPv6.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) : P4A.state state sz :=
    match s with
    | ParseEth =>
      {| st_op := extract(HdrEth);
        st_trans := transition select (| (EHdr (sz := sz) HdrEth)[111--96] |)
                                {{ [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|0|1|1|1 |] ==> inl ParseMPLS ;;;
                                  [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|1|0|0|0 |] ==> inl ParseMPLS ;;;
                                  [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl ParseEthv4 ;;;
                                  [| exact #b|1|0|0|0|0|1|1|0|1|1|0|1|1|1|0|1 |] ==> inl ParseEthv6 ;;;
                                  reject }}
      |}
    | ParseEthv4 =>
      {| st_op := extract(HdrIPVer);
         st_trans := transition inl ParseIPv4
      |}
    | ParseEthv6 =>
      {| st_op := extract(HdrIPVer);
         st_trans := transition inl ParseIPv6
      |}
    | ParseMPLS =>
      {| st_op := extract(HdrMPLS);
        st_trans := transition select (| (EHdr HdrMPLS)[24--24] |)
                                {{ [| hexact 0 |] ==> inl ParseMPLS ;;;
                                  [| hexact 1 |] ==> inl ParseIPVer ;;;
                                  reject
                                }}
      |}
    | ParseIPVer =>
      {| st_op := extract(HdrIPVer);
        st_trans := transition select (| EHdr HdrIPVer |)
                                {{ [| exact #b|0|1|0|0 |] ==> inl ParseIPv4;;;
                                  [| exact #b|0|1|1|0 |] ==> inl ParseIPv6;;;
                                  reject
                                }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIHL);
        st_trans := transition select (| EHdr HdrIHL |)
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

  Inductive state := | State_1_suff_2 | State_0_suff_2 | State_2_suff_0 | State_0_suff_1 | State_1_suff_1 | State_1 | State_0_suff_3 | State_4 | State_2 | State_1_suff_3 | State_0  | State_1_suff_0 | State_4_suff_0 | State_4_body.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | buf_320
  | buf_112
  | buf_16
  | buf_32
  | buf_240
  | buf_144
  | buf_176
  | buf_208
  | buf_304
  | buf_48.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition sz (h: header): nat :=
    match h with
    | buf_320 => 320
    | buf_112 => 112
    | buf_16 => 16
    | buf_32 => 32
    | buf_240 => 240
    | buf_144 => 144
    | buf_176 => 176
    | buf_208 => 208
    | buf_304 => 304
    | buf_48 => 48
    end.

  Definition states (s: state) :=
  match s with
  | State_0 => {|
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr (sz := sz) buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[111 -- 111], (EHdr buf_112)[110 -- 110], (EHdr buf_112)[109 -- 109], (EHdr buf_112)[108 -- 108], (EHdr buf_112)[107 -- 107], (EHdr buf_112)[106 -- 106], (EHdr buf_112)[105 -- 105], (EHdr buf_112)[104 -- 104], (EHdr buf_112)[103 -- 103], (EHdr buf_112)[102 -- 102], (EHdr buf_112)[101 -- 101], (EHdr buf_112)[100 -- 100], (EHdr buf_112)[99 -- 99], (EHdr buf_112)[98 -- 98], (EHdr buf_112)[97 -- 97], (EHdr buf_112)[96 -- 96]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_1 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1 |] ==> inl State_0_suff_1 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|1 |] ==> inl State_0_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_0_suff_3 ;;;
      reject
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
    st_trans := transition select (| (EHdr (sz := sz) buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_0 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_1 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_2 ;;;
      [| *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_3 ;;;
      reject
    }}
  |}
  | State_1_suff_0 => {|
    st_op := extract(buf_144);
    st_trans := transition accept;
  |}
  | State_1_suff_1 => {|
    st_op := extract(buf_176);
    st_trans := transition accept;
  |}
  | State_1_suff_2 => {|
    st_op := extract(buf_208);
    st_trans := transition accept;
  |}
  | State_1_suff_3 => {|
    st_op := extract(buf_240);
    st_trans := transition accept;
  |}
  | State_2 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_0 ;;;
      reject
    }}
  |}
  | State_2_suff_0 => {|
    st_op := extract(buf_304);
    st_trans := transition accept;
  |}
  | State_4 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr (sz := sz) buf_16)[15--12], (EHdr buf_16)[8--8] |) {{
      [| exact #b|0|1|0|0, exact #b|1 |] ==> inl State_1 ;;;
      [| exact #b|0|1|1|0, exact #b|1 |] ==> inl State_2 ;;;
      [| *, exact #b|0 |] ==> inl State_4_body ;;;
       reject
    }}
  |}
  | State_4_body => {|
    st_op := extract(buf_32);
    st_trans := transition select (| (EHdr (sz := sz) buf_32)[31 -- 31], (EHdr buf_32)[30 -- 30], (EHdr buf_32)[29 -- 29], (EHdr buf_32)[28 -- 28], (EHdr buf_32)[27 -- 27], (EHdr buf_32)[26 -- 26], (EHdr buf_32)[25 -- 25], (EHdr buf_32)[24 -- 24], (EHdr buf_32)[23 -- 23], (EHdr buf_32)[22 -- 22], (EHdr buf_32)[21 -- 21], (EHdr buf_32)[20 -- 20], (EHdr buf_32)[19 -- 19], (EHdr buf_32)[18 -- 18], (EHdr buf_32)[17 -- 17], (EHdr buf_32)[16 -- 16]|) {{
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_4_suff_0 ;;;
      reject
    }}
  |}
  | State_4_suff_0 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_4;
  |}
end.
Program Definition aut: Syntax.t state sz :=
  {| t_states := states |}.
Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End Optimized.
