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
Inductive state := | State_0_suff_1 | State_0_suff_2 | State_3_suff_2 | State_3_suff_1 | State_0_suff_3 | State_2_suff_0 | State_1_suff_0 | State_1 | State_3_suff_3 | State_4 | State_3_suff_0 | State_0 | State_3 | State_2.
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

Definition states (s: state) :=
  match s with
  | State_0 => {|
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr' buf_112)[15 -- 15], (EHdr' buf_112)[14 -- 14], (EHdr' buf_112)[13 -- 13], (EHdr' buf_112)[12 -- 12], (EHdr' buf_112)[11 -- 11], (EHdr' buf_112)[10 -- 10], (EHdr' buf_112)[9 -- 9], (EHdr' buf_112)[8 -- 8], (EHdr' buf_112)[7 -- 7], (EHdr' buf_112)[6 -- 6], (EHdr' buf_112)[5 -- 5], (EHdr' buf_112)[4 -- 4], (EHdr' buf_112)[3 -- 3], (EHdr' buf_112)[2 -- 2], (EHdr' buf_112)[1 -- 1], (EHdr' buf_112)[0 -- 0], (EHdr' buf_112)[111 -- 111], (EHdr' buf_112)[110 -- 110], (EHdr' buf_112)[109 -- 109], (EHdr' buf_112)[108 -- 108], (EHdr' buf_112)[107 -- 107], (EHdr' buf_112)[106 -- 106], (EHdr' buf_112)[105 -- 105], (EHdr' buf_112)[104 -- 104], (EHdr' buf_112)[103 -- 103], (EHdr' buf_112)[102 -- 102], (EHdr' buf_112)[101 -- 101], (EHdr' buf_112)[100 -- 100], (EHdr' buf_112)[99 -- 99], (EHdr' buf_112)[98 -- 98], (EHdr' buf_112)[97 -- 97], (EHdr' buf_112)[96 -- 96], (EHdr' buf_112)[15 -- 15], (EHdr' buf_112)[14 -- 14], (EHdr' buf_112)[13 -- 13], (EHdr' buf_112)[12 -- 12], (EHdr' buf_112)[11 -- 11], (EHdr' buf_112)[10 -- 10], (EHdr' buf_112)[9 -- 9], (EHdr' buf_112)[8 -- 8], (EHdr' buf_112)[7 -- 7], (EHdr' buf_112)[6 -- 6], (EHdr' buf_112)[5 -- 5], (EHdr' buf_112)[4 -- 4], (EHdr' buf_112)[3 -- 3], (EHdr' buf_112)[2 -- 2], (EHdr' buf_112)[1 -- 1], (EHdr' buf_112)[0 -- 0], (EHdr' buf_112)[15 -- 15], (EHdr' buf_112)[14 -- 14], (EHdr' buf_112)[13 -- 13], (EHdr' buf_112)[12 -- 12], (EHdr' buf_112)[11 -- 11], (EHdr' buf_112)[10 -- 10], (EHdr' buf_112)[9 -- 9], (EHdr' buf_112)[8 -- 8], (EHdr' buf_112)[7 -- 7], (EHdr' buf_112)[6 -- 6], (EHdr' buf_112)[5 -- 5], (EHdr' buf_112)[4 -- 4], (EHdr' buf_112)[3 -- 3], (EHdr' buf_112)[2 -- 2], (EHdr' buf_112)[1 -- 1], (EHdr' buf_112)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_1 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_3 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      reject
    }}
  |}
  | State_0_suff_1 => {|
    st_op := extract(buf_320);
    st_trans := transition accept;
  |}
  | State_0_suff_2 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_2;
  |}
  | State_0_suff_3 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_3;
  |}
  | State_1 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_0 ;;;
      reject
    }}
  |}
  | State_1_suff_0 => {|
    st_op := extract(buf_128);
    st_trans := transition accept;
  |}
  | State_2 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_0 ;;;
      reject
    }}
  |}
  | State_2_suff_0 => {|
    st_op := extract(buf_304);
    st_trans := transition accept;
  |}
  | State_3 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0], (EHdr' buf_16)[15 -- 15], (EHdr' buf_16)[14 -- 14], (EHdr' buf_16)[13 -- 13], (EHdr' buf_16)[12 -- 12], (EHdr' buf_16)[11 -- 11], (EHdr' buf_16)[10 -- 10], (EHdr' buf_16)[9 -- 9], (EHdr' buf_16)[8 -- 8], (EHdr' buf_16)[7 -- 7], (EHdr' buf_16)[6 -- 6], (EHdr' buf_16)[5 -- 5], (EHdr' buf_16)[4 -- 4], (EHdr' buf_16)[3 -- 3], (EHdr' buf_16)[2 -- 2], (EHdr' buf_16)[1 -- 1], (EHdr' buf_16)[0 -- 0]|) {{
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_0 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_1 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_2 ;;;
      [| *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_3 ;;;
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
    st_op := extract(buf_64);
    st_trans := transition select (| (EHdr' buf_64)[15 -- 15], (EHdr' buf_64)[14 -- 14], (EHdr' buf_64)[13 -- 13], (EHdr' buf_64)[12 -- 12], (EHdr' buf_64)[11 -- 11], (EHdr' buf_64)[10 -- 10], (EHdr' buf_64)[9 -- 9], (EHdr' buf_64)[8 -- 8], (EHdr' buf_64)[7 -- 7], (EHdr' buf_64)[6 -- 6], (EHdr' buf_64)[5 -- 5], (EHdr' buf_64)[4 -- 4], (EHdr' buf_64)[3 -- 3], (EHdr' buf_64)[2 -- 2], (EHdr' buf_64)[1 -- 1], (EHdr' buf_64)[0 -- 0], (EHdr' buf_64)[31 -- 31], (EHdr' buf_64)[30 -- 30], (EHdr' buf_64)[29 -- 29], (EHdr' buf_64)[28 -- 28], (EHdr' buf_64)[27 -- 27], (EHdr' buf_64)[26 -- 26], (EHdr' buf_64)[25 -- 25], (EHdr' buf_64)[24 -- 24], (EHdr' buf_64)[23 -- 23], (EHdr' buf_64)[22 -- 22], (EHdr' buf_64)[21 -- 21], (EHdr' buf_64)[20 -- 20], (EHdr' buf_64)[19 -- 19], (EHdr' buf_64)[18 -- 18], (EHdr' buf_64)[17 -- 17], (EHdr' buf_64)[16 -- 16], (EHdr' buf_64)[47 -- 47], (EHdr' buf_64)[46 -- 46], (EHdr' buf_64)[45 -- 45], (EHdr' buf_64)[44 -- 44], (EHdr' buf_64)[43 -- 43], (EHdr' buf_64)[42 -- 42], (EHdr' buf_64)[41 -- 41], (EHdr' buf_64)[40 -- 40], (EHdr' buf_64)[39 -- 39], (EHdr' buf_64)[38 -- 38], (EHdr' buf_64)[37 -- 37], (EHdr' buf_64)[36 -- 36], (EHdr' buf_64)[35 -- 35], (EHdr' buf_64)[34 -- 34], (EHdr' buf_64)[33 -- 33], (EHdr' buf_64)[32 -- 32], (EHdr' buf_64)[63 -- 63], (EHdr' buf_64)[62 -- 62], (EHdr' buf_64)[61 -- 61], (EHdr' buf_64)[60 -- 60], (EHdr' buf_64)[59 -- 59], (EHdr' buf_64)[58 -- 58], (EHdr' buf_64)[57 -- 57], (EHdr' buf_64)[56 -- 56], (EHdr' buf_64)[55 -- 55], (EHdr' buf_64)[54 -- 54], (EHdr' buf_64)[53 -- 53], (EHdr' buf_64)[52 -- 52], (EHdr' buf_64)[51 -- 51], (EHdr' buf_64)[50 -- 50], (EHdr' buf_64)[49 -- 49], (EHdr' buf_64)[48 -- 48]|) {{
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_1 extracting only 48 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_3 extracting only 48 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_2 extracting only 48 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to accept extracting only 48 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_1 extracting only 16 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_3 extracting only 16 *) ;;;
      [| *, *, *, *, *, *, *, exact #b|1, *, *, *, *, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to inl State_2 extracting only 16 *) ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject (* overflow, transition to accept extracting only 16 *) ;;;
      reject
    }}
  |}
end.
Program Definition aut: Syntax.t state sz :=
  {| t_states := states |}.
Solve Obligations with (destruct h || destruct s; cbv; Lia.lia).
  
