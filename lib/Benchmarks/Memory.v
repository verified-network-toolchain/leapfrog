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

Ltac prep_equiv :=
  unfold Equivalence.equiv, RelationClasses.complement in *;
  program_simpl; try congruence.

Obligation Tactic := prep_equiv.

Module MemoryWide.
  Inductive state :=
  | start
  | state_0
  | state_1
  | state_2
  | state_3
  | state_4
  | state_5
  | state_6
  | state_7
  | state_8
  | state_9
  | state_10
  | state_11
  | state_12
  | state_13
  | state_14
  | state_15
  | state_16
  | state_17
  | state_18
  | state_19
  | state_20
  | state_21
  | state_22
  | state_23
  | state_24
  | state_25
  | state_26
  | state_27
  | state_28
  | state_29
  | state_30
  | state_31
  | finish.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header := | Scratch1 | Val.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch1 => 1
    | Val => 5
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | start =>
      {| st_op := extract(Val) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) Val |) {{
            [| exact #b|0|0|0|0|0 |] ==> inl state_0 ;;;
            [| exact #b|0|0|0|0|1 |] ==> inl state_1 ;;;
            [| exact #b|0|0|0|1|0 |] ==> inl state_2 ;;;
            [| exact #b|0|0|0|1|1 |] ==> inl state_3 ;;;
            [| exact #b|0|0|1|0|0 |] ==> inl state_4 ;;;
            [| exact #b|0|0|1|0|1 |] ==> inl state_5 ;;;
            [| exact #b|0|0|1|1|0 |] ==> inl state_6 ;;;
            [| exact #b|0|0|1|1|1 |] ==> inl state_7 ;;;
            [| exact #b|0|1|0|0|0 |] ==> inl state_8 ;;;
            [| exact #b|0|1|0|0|1 |] ==> inl state_9 ;;;
            [| exact #b|0|1|0|1|0 |] ==> inl state_10 ;;;
            [| exact #b|0|1|0|1|1 |] ==> inl state_11 ;;;
            [| exact #b|0|1|1|0|0 |] ==> inl state_12 ;;;
            [| exact #b|0|1|1|0|1 |] ==> inl state_13 ;;;
            [| exact #b|0|1|1|1|0 |] ==> inl state_14 ;;;
            [| exact #b|0|1|1|1|1 |] ==> inl state_15 ;;;
            [| exact #b|1|0|0|0|0 |] ==> inl state_16 ;;;
            [| exact #b|1|0|0|0|1 |] ==> inl state_17 ;;;
            [| exact #b|1|0|0|1|0 |] ==> inl state_18 ;;;
            [| exact #b|1|0|0|1|1 |] ==> inl state_19 ;;;
            [| exact #b|1|0|1|0|0 |] ==> inl state_20 ;;;
            [| exact #b|1|0|1|0|1 |] ==> inl state_21 ;;;
            [| exact #b|1|0|1|1|0 |] ==> inl state_22 ;;;
            [| exact #b|1|0|1|1|1 |] ==> inl state_23 ;;;
            [| exact #b|1|1|0|0|0 |] ==> inl state_24 ;;;
            [| exact #b|1|1|0|0|1 |] ==> inl state_25 ;;;
            [| exact #b|1|1|0|1|0 |] ==> inl state_26 ;;;
            [| exact #b|1|1|0|1|1 |] ==> inl state_27 ;;;
            [| exact #b|1|1|1|0|0 |] ==> inl state_28 ;;;
            [| exact #b|1|1|1|0|1 |] ==> inl state_29 ;;;
            [| exact #b|1|1|1|1|0 |] ==> inl state_30 ;;;
            [| exact #b|1|1|1|1|1 |] ==> inl state_31 ;;;
            reject
         }}
      |}
    | state_0 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_1 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_2 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_3 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_4 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_5 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_6 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_7 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_8 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_9 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_10 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_11 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_12 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_13 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_14 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_15 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_16 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_17 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_18 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_19 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_20 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_21 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_22 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_23 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_24 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_25 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_26 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_27 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_28 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_29 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_30 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_31 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | finish => {| 
        st_op := extract(Scratch1);
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End MemoryWide.

Module WideSelf.
  Definition aut := Sum.sum MemoryWide.aut MemoryWide.aut.
End WideSelf.

Module MemoryTall.
  Inductive state := 
| state_1
| state_0
| state_11
| state_10
| state_01
| state_00
| state_111
| state_110
| state_101
| state_100
| state_011
| state_010
| state_001
| state_000
| state_1111
| state_1110
| state_1101
| state_1100
| state_1011
| state_1010
| state_1001
| state_1000
| state_0111
| state_0110
| state_0101
| state_0100
| state_0011
| state_0010
| state_0001
| state_0000
| state_11111
| state_11110
| state_11101
| state_11100
| state_11011
| state_11010
| state_11001
| state_11000
| state_10111
| state_10110
| state_10101
| state_10100
| state_10011
| state_10010
| state_10001
| state_10000
| state_01111
| state_01110
| state_01101
| state_01100
| state_01011
| state_01010
| state_01001
| state_01000
| state_00111
| state_00110
| state_00101
| state_00100
| state_00011
| state_00010
| state_00001
| state_00000
| state_111111
| state_111110
| state_111101
| state_111100
| state_111011
| state_111010
| state_111001
| state_111000
| state_110111
| state_110110
| state_110101
| state_110100
| state_110011
| state_110010
| state_110001
| state_110000
| state_101111
| state_101110
| state_101101
| state_101100
| state_101011
| state_101010
| state_101001
| state_101000
| state_100111
| state_100110
| state_100101
| state_100100
| state_100011
| state_100010
| state_100001
| state_100000
| state_011111
| state_011110
| state_011101
| state_011100
| state_011011
| state_011010
| state_011001
| state_011000
| state_010111
| state_010110
| state_010101
| state_010100
| state_010011
| state_010010
| state_010001
| state_010000
| state_001111
| state_001110
| state_001101
| state_001100
| state_001011
| state_001010
| state_001001
| state_001000
| state_000111
| state_000110
| state_000101
| state_000100
| state_000011
| state_000010
| state_000001
| state_000000
  | start .

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header := | Scratch1 | Val.
  Definition sz (h: header) : nat :=
    match h with
    | Scratch1 => 1
    | Val => 6
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) := 
    match s with
    | start => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_0 ;;; [| exact #b|1 |] ==> inl state_1 ;;; reject }} |}
    | state_1 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_10 ;;; [| exact #b|1 |] ==> inl state_11 ;;; reject }} |}
| state_0 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_00 ;;; [| exact #b|1 |] ==> inl state_01 ;;; reject }} |}
| state_11 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_110 ;;; [| exact #b|1 |] ==> inl state_111 ;;; reject }} |}
| state_10 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_100 ;;; [| exact #b|1 |] ==> inl state_101 ;;; reject }} |}
| state_01 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_010 ;;; [| exact #b|1 |] ==> inl state_011 ;;; reject }} |}
| state_00 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_000 ;;; [| exact #b|1 |] ==> inl state_001 ;;; reject }} |}
| state_111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_1110 ;;; [| exact #b|1 |] ==> inl state_1111 ;;; reject }} |}
| state_110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_1100 ;;; [| exact #b|1 |] ==> inl state_1101 ;;; reject }} |}
| state_101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_1010 ;;; [| exact #b|1 |] ==> inl state_1011 ;;; reject }} |}
| state_100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_1000 ;;; [| exact #b|1 |] ==> inl state_1001 ;;; reject }} |}
| state_011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_0110 ;;; [| exact #b|1 |] ==> inl state_0111 ;;; reject }} |}
| state_010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_0100 ;;; [| exact #b|1 |] ==> inl state_0101 ;;; reject }} |}
| state_001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_0010 ;;; [| exact #b|1 |] ==> inl state_0011 ;;; reject }} |}
| state_000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_0000 ;;; [| exact #b|1 |] ==> inl state_0001 ;;; reject }} |}
| state_1111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_11110 ;;; [| exact #b|1 |] ==> inl state_11111 ;;; reject }} |}
| state_1110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_11100 ;;; [| exact #b|1 |] ==> inl state_11101 ;;; reject }} |}
| state_1101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_11010 ;;; [| exact #b|1 |] ==> inl state_11011 ;;; reject }} |}
| state_1100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_11000 ;;; [| exact #b|1 |] ==> inl state_11001 ;;; reject }} |}
| state_1011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_10110 ;;; [| exact #b|1 |] ==> inl state_10111 ;;; reject }} |}
| state_1010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_10100 ;;; [| exact #b|1 |] ==> inl state_10101 ;;; reject }} |}
| state_1001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_10010 ;;; [| exact #b|1 |] ==> inl state_10011 ;;; reject }} |}
| state_1000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_10000 ;;; [| exact #b|1 |] ==> inl state_10001 ;;; reject }} |}
| state_0111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_01110 ;;; [| exact #b|1 |] ==> inl state_01111 ;;; reject }} |}
| state_0110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_01100 ;;; [| exact #b|1 |] ==> inl state_01101 ;;; reject }} |}
| state_0101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_01010 ;;; [| exact #b|1 |] ==> inl state_01011 ;;; reject }} |}
| state_0100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_01000 ;;; [| exact #b|1 |] ==> inl state_01001 ;;; reject }} |}
| state_0011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_00110 ;;; [| exact #b|1 |] ==> inl state_00111 ;;; reject }} |}
| state_0010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_00100 ;;; [| exact #b|1 |] ==> inl state_00101 ;;; reject }} |}
| state_0001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_00010 ;;; [| exact #b|1 |] ==> inl state_00011 ;;; reject }} |}
| state_0000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_00000 ;;; [| exact #b|1 |] ==> inl state_00001 ;;; reject }} |}
| state_11111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_111110 ;;; [| exact #b|1 |] ==> inl state_111111 ;;; reject }} |}
| state_11110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_111100 ;;; [| exact #b|1 |] ==> inl state_111101 ;;; reject }} |}
| state_11101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_111010 ;;; [| exact #b|1 |] ==> inl state_111011 ;;; reject }} |}
| state_11100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_111000 ;;; [| exact #b|1 |] ==> inl state_111001 ;;; reject }} |}
| state_11011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_110110 ;;; [| exact #b|1 |] ==> inl state_110111 ;;; reject }} |}
| state_11010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_110100 ;;; [| exact #b|1 |] ==> inl state_110101 ;;; reject }} |}
| state_11001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_110010 ;;; [| exact #b|1 |] ==> inl state_110011 ;;; reject }} |}
| state_11000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_110000 ;;; [| exact #b|1 |] ==> inl state_110001 ;;; reject }} |}
| state_10111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_101110 ;;; [| exact #b|1 |] ==> inl state_101111 ;;; reject }} |}
| state_10110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_101100 ;;; [| exact #b|1 |] ==> inl state_101101 ;;; reject }} |}
| state_10101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_101010 ;;; [| exact #b|1 |] ==> inl state_101011 ;;; reject }} |}
| state_10100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_101000 ;;; [| exact #b|1 |] ==> inl state_101001 ;;; reject }} |}
| state_10011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_100110 ;;; [| exact #b|1 |] ==> inl state_100111 ;;; reject }} |}
| state_10010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_100100 ;;; [| exact #b|1 |] ==> inl state_100101 ;;; reject }} |}
| state_10001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_100010 ;;; [| exact #b|1 |] ==> inl state_100011 ;;; reject }} |}
| state_10000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_100000 ;;; [| exact #b|1 |] ==> inl state_100001 ;;; reject }} |}
| state_01111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_011110 ;;; [| exact #b|1 |] ==> inl state_011111 ;;; reject }} |}
| state_01110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_011100 ;;; [| exact #b|1 |] ==> inl state_011101 ;;; reject }} |}
| state_01101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_011010 ;;; [| exact #b|1 |] ==> inl state_011011 ;;; reject }} |}
| state_01100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_011000 ;;; [| exact #b|1 |] ==> inl state_011001 ;;; reject }} |}
| state_01011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_010110 ;;; [| exact #b|1 |] ==> inl state_010111 ;;; reject }} |}
| state_01010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_010100 ;;; [| exact #b|1 |] ==> inl state_010101 ;;; reject }} |}
| state_01001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_010010 ;;; [| exact #b|1 |] ==> inl state_010011 ;;; reject }} |}
| state_01000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_010000 ;;; [| exact #b|1 |] ==> inl state_010001 ;;; reject }} |}
| state_00111 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_001110 ;;; [| exact #b|1 |] ==> inl state_001111 ;;; reject }} |}
| state_00110 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_001100 ;;; [| exact #b|1 |] ==> inl state_001101 ;;; reject }} |}
| state_00101 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_001010 ;;; [| exact #b|1 |] ==> inl state_001011 ;;; reject }} |}
| state_00100 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_001000 ;;; [| exact #b|1 |] ==> inl state_001001 ;;; reject }} |}
| state_00011 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_000110 ;;; [| exact #b|1 |] ==> inl state_000111 ;;; reject }} |}
| state_00010 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_000100 ;;; [| exact #b|1 |] ==> inl state_000101 ;;; reject }} |}
| state_00001 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_000010 ;;; [| exact #b|1 |] ==> inl state_000011 ;;; reject }} |}
| state_00000 => {| st_op := extract(Scratch1) ; st_trans := transition select (| EHdr (Hdr_sz := sz) Scratch1 |) {{ [| exact #b|0 |] ==> inl state_000000 ;;; [| exact #b|1 |] ==> inl state_000001 ;;; reject }} |}
| state_111111 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|1|1|1 ; st_trans := transition accept  |}
| state_111110 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|1|1|0 ; st_trans := transition accept  |}
| state_111101 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|1|0|1 ; st_trans := transition accept  |}
| state_111100 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|1|0|0 ; st_trans := transition accept  |}
| state_111011 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|0|1|1 ; st_trans := transition accept  |}
| state_111010 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|0|1|0 ; st_trans := transition accept  |}
| state_111001 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|0|0|1 ; st_trans := transition accept  |}
| state_111000 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|1|0|0|0 ; st_trans := transition accept  |}
| state_110111 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|1|1|1 ; st_trans := transition accept  |}
| state_110110 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|1|1|0 ; st_trans := transition accept  |}
| state_110101 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|1|0|1 ; st_trans := transition accept  |}
| state_110100 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|1|0|0 ; st_trans := transition accept  |}
| state_110011 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|0|1|1 ; st_trans := transition accept  |}
| state_110010 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|0|1|0 ; st_trans := transition accept  |}
| state_110001 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|0|0|1 ; st_trans := transition accept  |}
| state_110000 => {| st_op := extract(Scratch1) ;; Val <- #be|1|1|0|0|0|0 ; st_trans := transition accept  |}
| state_101111 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|1|1|1 ; st_trans := transition accept  |}
| state_101110 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|1|1|0 ; st_trans := transition accept  |}
| state_101101 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|1|0|1 ; st_trans := transition accept  |}
| state_101100 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|1|0|0 ; st_trans := transition accept  |}
| state_101011 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|0|1|1 ; st_trans := transition accept  |}
| state_101010 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|0|1|0 ; st_trans := transition accept  |}
| state_101001 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|0|0|1 ; st_trans := transition accept  |}
| state_101000 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|1|0|0|0 ; st_trans := transition accept  |}
| state_100111 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|1|1|1 ; st_trans := transition accept  |}
| state_100110 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|1|1|0 ; st_trans := transition accept  |}
| state_100101 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|1|0|1 ; st_trans := transition accept  |}
| state_100100 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|1|0|0 ; st_trans := transition accept  |}
| state_100011 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|0|1|1 ; st_trans := transition accept  |}
| state_100010 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|0|1|0 ; st_trans := transition accept  |}
| state_100001 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|0|0|1 ; st_trans := transition accept  |}
| state_100000 => {| st_op := extract(Scratch1) ;; Val <- #be|1|0|0|0|0|0 ; st_trans := transition accept  |}
| state_011111 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|1|1|1 ; st_trans := transition accept  |}
| state_011110 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|1|1|0 ; st_trans := transition accept  |}
| state_011101 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|1|0|1 ; st_trans := transition accept  |}
| state_011100 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|1|0|0 ; st_trans := transition accept  |}
| state_011011 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|0|1|1 ; st_trans := transition accept  |}
| state_011010 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|0|1|0 ; st_trans := transition accept  |}
| state_011001 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|0|0|1 ; st_trans := transition accept  |}
| state_011000 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|1|0|0|0 ; st_trans := transition accept  |}
| state_010111 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|1|1|1 ; st_trans := transition accept  |}
| state_010110 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|1|1|0 ; st_trans := transition accept  |}
| state_010101 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|1|0|1 ; st_trans := transition accept  |}
| state_010100 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|1|0|0 ; st_trans := transition accept  |}
| state_010011 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|0|1|1 ; st_trans := transition accept  |}
| state_010010 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|0|1|0 ; st_trans := transition accept  |}
| state_010001 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|0|0|1 ; st_trans := transition accept  |}
| state_010000 => {| st_op := extract(Scratch1) ;; Val <- #be|0|1|0|0|0|0 ; st_trans := transition accept  |}
| state_001111 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|1|1|1 ; st_trans := transition accept  |}
| state_001110 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|1|1|0 ; st_trans := transition accept  |}
| state_001101 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|1|0|1 ; st_trans := transition accept  |}
| state_001100 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|1|0|0 ; st_trans := transition accept  |}
| state_001011 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|0|1|1 ; st_trans := transition accept  |}
| state_001010 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|0|1|0 ; st_trans := transition accept  |}
| state_001001 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|0|0|1 ; st_trans := transition accept  |}
| state_001000 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|1|0|0|0 ; st_trans := transition accept  |}
| state_000111 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|1|1|1 ; st_trans := transition accept  |}
| state_000110 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|1|1|0 ; st_trans := transition accept  |}
| state_000101 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|1|0|1 ; st_trans := transition accept  |}
| state_000100 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|1|0|0 ; st_trans := transition accept  |}
| state_000011 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|0|1|1 ; st_trans := transition accept  |}
| state_000010 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|0|1|0 ; st_trans := transition accept  |}
| state_000001 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|0|0|1 ; st_trans := transition accept  |}
| state_000000 => {| st_op := extract(Scratch1) ;; Val <- #be|0|0|0|0|0|0 ; st_trans := transition accept  |}
    end.


  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End MemoryTall.

Module TallSelf.
  Definition aut := Sum.sum MemoryTall.aut MemoryTall.aut.
End TallSelf.

Module MemoryWide16.
  Inductive state :=
  | start
  | state_0
  | state_1
  | state_2
  | state_3
  | state_4
  | state_5
  | state_6
  | state_7
  | state_8
  | state_9
  | state_10
  | state_11
  | state_12
  | state_13
  | state_14
  | state_15
  | finish.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive header := | Scratch1 | Val.

  Definition sz (h: header) : nat :=
    match h with
    | Scratch1 => 1
    | Val => 4
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Definition states (s: state) :=
    match s with
    | start =>
      {| st_op := extract(Val) ;
         st_trans := transition select (| EHdr (Hdr_sz := sz) Val |) {{
            [| exact #b|0|0|0|0 |] ==> inl state_0 ;;;
            [| exact #b|0|0|0|1 |] ==> inl state_1 ;;;
            [| exact #b|0|0|1|0 |] ==> inl state_2 ;;;
            [| exact #b|0|0|1|1 |] ==> inl state_3 ;;;
            [| exact #b|0|1|0|0 |] ==> inl state_4 ;;;
            [| exact #b|0|1|0|1 |] ==> inl state_5 ;;;
            [| exact #b|0|1|1|0 |] ==> inl state_6 ;;;
            [| exact #b|0|1|1|1 |] ==> inl state_7 ;;;
            [| exact #b|1|0|0|0 |] ==> inl state_8 ;;;
            [| exact #b|1|0|0|1 |] ==> inl state_9 ;;;
            [| exact #b|1|0|1|0 |] ==> inl state_10 ;;;
            [| exact #b|1|0|1|1 |] ==> inl state_11 ;;;
            [| exact #b|1|1|0|0 |] ==> inl state_12 ;;;
            [| exact #b|1|1|0|1 |] ==> inl state_13 ;;;
            [| exact #b|1|1|1|0 |] ==> inl state_14 ;;;
            [| exact #b|1|1|1|1 |] ==> inl state_15 ;;;
            reject
         }}
      |}
    | state_0 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_1 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_2 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_3 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_4 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_5 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_6 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_7 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_8 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_9 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_10 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_11 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_12 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_13 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_14 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | state_15 => {| st_op := extract(Scratch1); st_trans := transition inl finish |}
    | finish => {| 
        st_op := extract(Scratch1);
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (destruct s || destruct h; cbv; Lia.lia).

End MemoryWide16.

Module Wide16Self.
  Definition aut := Sum.sum MemoryWide16.aut MemoryWide16.aut.
End Wide16Self.