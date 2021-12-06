Require Coq.Classes.EquivDec.
Require Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.Program.Program.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.Sum.
Require Import Poulet4.P4automata.Syntax.
Require Import Poulet4.P4automata.BisimChecker.

Require Import Poulet4.P4automata.Notations.

Open Scope p4a.

Module VerySimple.
  Inductive state := | Ethernet | VLan1 | VLan2 | IPV4.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header :=
  | H_Eth
  | H_VLan
  | H_IP.

  Definition sz (h: header): nat :=
    match h with
    | H_Eth => 112
    | H_VLan => 32
    | H_IP => 160
    end.

  Definition states (s: state) :=
    match s with
    | Ethernet => {|
      st_op := extract(H_Eth);
      st_trans := transition select (| (EHdr (sz := sz) H_Eth)[111 -- 96] |) {{
        [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl IPV4 ;;;
        [| exact #b|1|0|0|0|0|0|0|1|0|0|0|0|0|0|0|0 |] ==> inl VLan1 ;;;
        accept
      }}
    |}
    | VLan1 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr (sz := sz) H_VLan)[31 -- 16]|) {{
        [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl IPV4 ;;;
        [| exact #b|1|0|0|0|0|0|0|1|0|0|0|0|0|0|0|0 |] ==> inl VLan2 ;;;
        reject
      }}
    |}
    | VLan2 => {|
      st_op := extract(H_VLan);
      st_trans := transition select (| (EHdr (sz := sz) H_VLan)[31 -- 16]|) {{
        [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl IPV4 ;;;
        accept
      }}
    |}
    | IPV4 => {|
      st_op := extract(H_IP);
      st_trans := transition accept
    |}
    end.

    Program Definition aut: Syntax.t state sz :=
      {| t_states := states |}.
    Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End VerySimple.

Module Optimized.
Inductive state := | State_0 | State_0_suff_1 | State_1_suff_0 | State_1_suff_1 | State_0_suff_0 | State_1.
Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Instance state_finite: @Finite state _ state_eq_dec.
Proof.
  solve_finiteness.
Defined.

Inductive header :=
| buf_112
| buf_16
| buf_160
| buf_48
| buf_128.

Scheme Equality for header.
Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
Global Instance header_finite: @Finite header _ header_eq_dec.
Proof.
  solve_finiteness.
Defined.

Definition sz (h: header) :=
  match h with
  | buf_112 => 112
  | buf_16 => 16
  | buf_160 => 160
  | buf_48 => 48
  | buf_128 => 128
  end.

Definition states (s: state) :=
  match s with
  | State_0 => {|
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr (sz := sz) buf_112)[15 -- 15], (EHdr buf_112)[14 -- 14], (EHdr buf_112)[13 -- 13], (EHdr buf_112)[12 -- 12], (EHdr buf_112)[11 -- 11], (EHdr buf_112)[10 -- 10], (EHdr buf_112)[9 -- 9], (EHdr buf_112)[8 -- 8], (EHdr buf_112)[7 -- 7], (EHdr buf_112)[6 -- 6], (EHdr buf_112)[5 -- 5], (EHdr buf_112)[4 -- 4], (EHdr buf_112)[3 -- 3], (EHdr buf_112)[2 -- 2], (EHdr buf_112)[1 -- 1], (EHdr buf_112)[0 -- 0], (EHdr buf_112)[111 -- 111], (EHdr buf_112)[110 -- 110], (EHdr buf_112)[109 -- 109], (EHdr buf_112)[108 -- 108], (EHdr buf_112)[107 -- 107], (EHdr buf_112)[106 -- 106], (EHdr buf_112)[105 -- 105], (EHdr buf_112)[104 -- 104], (EHdr buf_112)[103 -- 103], (EHdr buf_112)[102 -- 102], (EHdr buf_112)[101 -- 101], (EHdr buf_112)[100 -- 100], (EHdr buf_112)[99 -- 99], (EHdr buf_112)[98 -- 98], (EHdr buf_112)[97 -- 97], (EHdr buf_112)[96 -- 96]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_0_suff_0 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_0_suff_1 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      reject
    }}
  |}
  | State_0_suff_0 => {|
    st_op := extract(buf_160);
    st_trans := transition accept;
  |}
  | State_0_suff_1 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_1;
  |}
  | State_1 => {|
    st_op := extract(buf_48);
    st_trans := transition select (| (EHdr (sz := sz) buf_48)[15 -- 15], (EHdr buf_48)[14 -- 14], (EHdr buf_48)[13 -- 13], (EHdr buf_48)[12 -- 12], (EHdr buf_48)[11 -- 11], (EHdr buf_48)[10 -- 10], (EHdr buf_48)[9 -- 9], (EHdr buf_48)[8 -- 8], (EHdr buf_48)[7 -- 7], (EHdr buf_48)[6 -- 6], (EHdr buf_48)[5 -- 5], (EHdr buf_48)[4 -- 4], (EHdr buf_48)[3 -- 3], (EHdr buf_48)[2 -- 2], (EHdr buf_48)[1 -- 1], (EHdr buf_48)[0 -- 0], (EHdr buf_48)[47 -- 47], (EHdr buf_48)[46 -- 46], (EHdr buf_48)[45 -- 45], (EHdr buf_48)[44 -- 44], (EHdr buf_48)[43 -- 43], (EHdr buf_48)[42 -- 42], (EHdr buf_48)[41 -- 41], (EHdr buf_48)[40 -- 40], (EHdr buf_48)[39 -- 39], (EHdr buf_48)[38 -- 38], (EHdr buf_48)[37 -- 37], (EHdr buf_48)[36 -- 36], (EHdr buf_48)[35 -- 35], (EHdr buf_48)[34 -- 34], (EHdr buf_48)[33 -- 33], (EHdr buf_48)[32 -- 32]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_0 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> inl State_1_suff_1 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      reject
    }}
  |}
  | State_1_suff_0 => {|
    st_op := extract(buf_128);
    st_trans := transition accept;
  |}
  | State_1_suff_1 => {|
    st_op := extract(buf_160);
    st_trans := transition accept;
  |}
end.
Program Definition aut: Syntax.t state sz :=
  {| t_states := states |}.
Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).
End Optimized.
