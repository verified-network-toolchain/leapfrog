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

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Open Scope p4a.

Module Simple.

  Notation eth_size := 112.
  Notation vlan_size := 160.
  Notation ipv4_size := 64.
  Notation ipv6_size := 64.
  Notation icmp_size := 32.
  Notation tcp_size := 160.
  Notation udp_size := 160.
  Notation arp_size := 64.

  Inductive header :=
  | HdrEth
  | HdrVLAN0
  | HdrVLAN1
  | HdrIPv4
  | HdrIPv6
  | HdrTCP
  | HdrUDP
  | HdrICMP
  | HdrICMPv6
  | HdrARP
  | HdrARPIP.

  Definition sz (h: header) : N :=
    match h with
    | HdrEth => 112
    | HdrVLAN0
    | HdrVLAN1 => 160
    | HdrIPv4 => 160
    | HdrIPv6 => 160
    | HdrTCP => 192
    | HdrUDP => 64
    | HdrICMP => 32
    | HdrICMPv6 => 32
    | HdrARP => 64
    | HdrARPIP => 64
    end.

  Scheme Equality for header.
  Global Instance header_eqdec: EquivDec.EqDec header eq := header_eq_dec.
  Global Instance header_finite: @Finite header _ header_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Inductive state: Type :=
  | ParseEth
  | ParseVLAN0
  | ParseVLAN1
  | ParseIPv4
  | ParseIPv6
  | ParseTCP
  | ParseUDP
  | ParseICMP
  | ParseICMPv6
  | ParseARP
  | ParseARPIP.

  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Instance state_finite: @Finite state _ state_eq_dec.
  Proof.
    solve_finiteness.
  Defined.

  Notation Ehdr := (EHdr (Hdr_sz := sz)).

  Definition states (s: state) : P4A.state state sz :=
    match s return P4A.state state sz with
    | ParseEth =>
      {| st_op := extract(HdrEth);
        st_trans := transition select (| (Ehdr HdrEth)[111--96] |)
                                {{ [| hexact_w(16) 0x8100 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact_w(16) 0x9100 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact_w(16) 0x9200 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact_w(16) 0x9300 |] ==> inl ParseVLAN0 ;;;
                                  [| hexact_w(16) 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact_w(16) 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact_w(16) 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact_w(16) 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseVLAN0 =>
      {| st_op := extract(HdrVLAN0) ;
        st_trans := transition select (| (Ehdr HdrVLAN0)[159--144] |)
                                {{ [| hexact_w(16) 0x8100 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact_w(16) 0x9100 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact_w(16) 0x9200 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact_w(16) 0x9300 |] ==> inl ParseVLAN1 ;;;
                                  [| hexact_w(16) 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact_w(16) 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact_w(16) 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact_w(16) 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseVLAN1 =>
      {| st_op := extract(HdrVLAN1) ;
        st_trans := transition select (| (Ehdr HdrVLAN1)[159--144] |)
                                {{ [| hexact_w(16) 0x0800 |] ==> inl ParseIPv4 ;;;
                                  [| hexact_w(16) 0x86dd |] ==> inl ParseIPv6 ;;;
                                  [| hexact_w(16) 0x0806 |] ==> inl ParseARP ;;;
                                  [| hexact_w(16) 0x8035 |] ==> inl ParseARP ;;;
                                  reject }}
      |}
    | ParseIPv4 =>
      {| st_op := extract(HdrIPv4);
        st_trans := transition select (| (Ehdr HdrIPv4)[79--72] |)
                                {{ [| hexact_w(8) 1 |] ==> inl ParseICMP;;;
                                  [| hexact_w(8) 6 |] ==> inl ParseTCP;;;
                                  [| hexact_w(8) 17 |] ==> inl ParseUDP;;;
                                  accept
                                }}
      |}
    | ParseIPv6 =>
      {| st_op := extract(HdrIPv6);
        st_trans := transition select (| (Ehdr HdrIPv6)[55--48] |)
                                {{ [| hexact_w(8) 1 |] ==> inl ParseICMPv6;;;
                                  [| hexact_w(8) 6 |] ==> inl ParseTCP;;;
                                  [| hexact_w(8) 17 |] ==> inl ParseUDP;;;
                                  accept
                                }}
      |}
    | ParseUDP =>
      {| st_op := extract(HdrUDP);
        st_trans := transition accept |}
    | ParseTCP =>
      {| st_op := extract(HdrTCP);
        st_trans := transition accept |}
    | ParseICMP =>
      {| st_op := extract(HdrICMP);
        st_trans := transition accept |}
    | ParseICMPv6 =>
      {| st_op := extract(HdrICMPv6);
        st_trans := transition accept |}
    | ParseARP =>
      {| st_op := extract(HdrARP);
        st_trans := transition select (| (Ehdr HdrARP)[31--16] |)
                                {{ [| hexact_w(16) 0x0800 |] ==> inl ParseARPIP;;;
                                  accept
                                }}
      |}
    | ParseARPIP =>
      {| st_op := extract(HdrARPIP);
        st_trans := transition accept
      |}
    end.

  Program Definition aut: Syntax.t state sz :=
    {| t_states := states |}.
  Solve Obligations with (try (destruct s; vm_compute; exact eq_refl) || (destruct h; simpl sz; Lia.lia)).

End Simple.
(*
Module Optimized.
Inductive state := | State_1_suff_12 | State_7_suff_3 | State_4_suff_0 | State_1 | State_0_suff_0 | State_2_suff_3 | State_6_suff_0 | State_7 | State_8 | State_9 | State_6_suff_3 | State_1_suff_11 | State_5_suff_2 | State_1_suff_7 | State_0 | State_8_suff_1 | State_4_suff_3 | State_3_suff_0 | State_2_suff_1 | State_5_suff_0 | State_9_suff_1 | State_4_suff_2 | State_8_suff_0 | State_5_suff_1 | State_9_suff_0 | State_7_suff_2 | State_2 | State_7_suff_0 | State_8_suff_3 | State_8_suff_2 | State_1_suff_10 | State_9_suff_3 | State_10_suff_1 | State_6_suff_1 | State_4_suff_1 | State_10 | State_3 | State_2_suff_0 | State_5 | State_6 | State_9_suff_2 | State_1_suff_6 | State_3_suff_1 | State_2_suff_2 | State_1_suff_3 | State_4 | State_6_suff_2 | State_9_suff_6 | State_1_suff_5 | State_7_suff_1 | State_10_suff_0 | State_5_suff_3.
Scheme Equality for state.
Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [State_1_suff_12; State_7_suff_3; State_4_suff_0; State_1; State_0_suff_0; State_2_suff_3; State_6_suff_0; State_7; State_8; State_9; State_6_suff_3; State_1_suff_11; State_5_suff_2; State_1_suff_7; State_0; State_8_suff_1; State_4_suff_3; State_3_suff_0; State_2_suff_1; State_5_suff_0; State_9_suff_1; State_4_suff_2; State_8_suff_0; State_5_suff_1; State_9_suff_0; State_7_suff_2; State_2; State_7_suff_0; State_8_suff_3; State_8_suff_2; State_1_suff_10; State_9_suff_3; State_10_suff_1; State_6_suff_1; State_4_suff_1; State_10; State_3; State_2_suff_0; State_5; State_6; State_9_suff_2; State_1_suff_6; State_3_suff_1; State_2_suff_2; State_1_suff_3; State_4; State_6_suff_2; State_9_suff_6; State_1_suff_5; State_7_suff_1; State_10_suff_0; State_5_suff_3] |}.
Next Obligation.
repeat constructor;
  repeat match goal with
          | H: List.In _ [] |- _ => apply List.in_nil in H; exfalso; exact H
          | |- ~ List.In _ [] => apply List.in_nil
          | |- ~ List.In _ (_ :: _) => unfold not; intros
          | H: List.In _ (_::_) |- _ => inversion H; clear H
          | _ => discriminate
          end.
Qed.
Next Obligation.
  destruct x; intuition congruence.
Qed.
Inductive header : nat -> Type :=
| buf_256: header 256
| buf_320: header 320
| buf_192: header 192
| buf_72: header 72
| buf_136: header 136
| buf_200: header 200
| buf_264: header 264
| buf_16: header 16
| buf_80: header 80
| buf_288: header 288
| buf_352: header 352
| buf_32: header 32
| buf_40: header 40
| buf_104: header 104
| buf_168: header 168
| buf_232: header 232
| buf_48: header 48.
Definition h256_eq_dec (x y: header 256) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_256 =>
    match y with
    | buf_256 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h320_eq_dec (x y: header 320) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_320 =>
    match y with
    | buf_320 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h192_eq_dec (x y: header 192) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_192 =>
    match y with
    | buf_192 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h288_eq_dec (x y: header 288) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_288 =>
    match y with
    | buf_288 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h352_eq_dec (x y: header 352) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_352 =>
    match y with
    | buf_352 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_32 =>
    match y with
    | buf_32 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h72_eq_dec (x y: header 72) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_72 =>
    match y with
    | buf_72 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h136_eq_dec (x y: header 136) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_136 =>
    match y with
    | buf_136 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h200_eq_dec (x y: header 200) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_200 =>
    match y with
    | buf_200 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h264_eq_dec (x y: header 264) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_264 =>
    match y with
    | buf_264 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h40_eq_dec (x y: header 40) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_40 =>
    match y with
    | buf_40 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h104_eq_dec (x y: header 104) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_104 =>
    match y with
    | buf_104 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h168_eq_dec (x y: header 168) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_168 =>
    match y with
    | buf_168 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h232_eq_dec (x y: header 232) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_232 =>
    match y with
    | buf_232 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h16_eq_dec (x y: header 16) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_16 =>
    match y with
    | buf_16 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h80_eq_dec (x y: header 80) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_80 =>
    match y with
    | buf_80 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h48_eq_dec (x y: header 48) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_48 =>
    match y with
    | buf_48 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Derive Signature for header.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h256_eq_dec) ::
     (existT _ _ h320_eq_dec) ::
     (existT _ _ h192_eq_dec) ::
     (existT _ _ h288_eq_dec) ::
     (existT _ _ h352_eq_dec) ::
     (existT _ _ h32_eq_dec) ::
     (existT _ _ h72_eq_dec) ::
     (existT _ _ h136_eq_dec) ::
     (existT _ _ h200_eq_dec) ::
     (existT _ _ h264_eq_dec) ::
     (existT _ _ h40_eq_dec) ::
     (existT _ _ h104_eq_dec) ::
     (existT _ _ h168_eq_dec) ::
     (existT _ _ h232_eq_dec) ::
     (existT _ _ h16_eq_dec) ::
     (existT _ _ h80_eq_dec) ::
     (existT _ _ h48_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [256; 320 ; 192 ; 288 ; 352 ; 32 ; 72 ; 136 ; 200 ; 264 ; 40 ; 104 ; 168 ; 232 ; 16 ; 80 ; 48 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ buf_256
    ; existT _ _ buf_320
    ; existT _ _ buf_192
    ; existT _ _ buf_72
    ; existT _ _ buf_136
    ; existT _ _ buf_200
    ; existT _ _ buf_264
    ; existT _ _ buf_16
    ; existT _ _ buf_80
    ; existT _ _ buf_288
    ; existT _ _ buf_352
    ; existT _ _ buf_32
    ; existT _ _ buf_40
    ; existT _ _ buf_104
    ; existT _ _ buf_168
    ; existT _ _ buf_232
    ; existT _ _ buf_48
    ] |}.
Next Obligation.
  solve_header_finite.
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
  | State_0 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (Ehdr buf_16)[15 -- 15], (Ehdr buf_16)[14 -- 14], (Ehdr buf_16)[13 -- 13], (Ehdr buf_16)[12 -- 12], (Ehdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_0_suff_0 ;;;
      reject
    }}
  |}
  | State_0_suff_0 => {|
    st_op := extract(buf_80);
    st_trans := transition inl State_0;
  |}
  | State_1 => {|
    st_op := extract(buf_48);
    st_trans := transition select (| (EHdr buf_48)[15 -- 15], (EHdr buf_48)[14 -- 14], (EHdr buf_48)[13 -- 13], (EHdr buf_48)[12 -- 12], (EHdr buf_48)[11 -- 11], (EHdr buf_48)[10 -- 10], (EHdr buf_48)[9 -- 9], (EHdr buf_48)[8 -- 8], (EHdr buf_48)[7 -- 7], (EHdr buf_48)[6 -- 6], (EHdr buf_48)[5 -- 5], (EHdr buf_48)[4 -- 4], (EHdr buf_48)[3 -- 3], (EHdr buf_48)[2 -- 2], (EHdr buf_48)[1 -- 1], (EHdr buf_48)[0 -- 0], (EHdr buf_48)[47 -- 47], (EHdr buf_48)[46 -- 46], (EHdr buf_48)[45 -- 45], (EHdr buf_48)[44 -- 44], (EHdr buf_48)[43 -- 43], (EHdr buf_48)[42 -- 42], (EHdr buf_48)[41 -- 41], (EHdr buf_48)[40 -- 40], (EHdr buf_48)[39 -- 39], (EHdr buf_48)[38 -- 38], (EHdr buf_48)[37 -- 37], (EHdr buf_48)[36 -- 36], (EHdr buf_48)[35 -- 35], (EHdr buf_48)[34 -- 34], (EHdr buf_48)[33 -- 33], (EHdr buf_48)[32 -- 32]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_1_suff_3 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0 |] ==> inl State_1_suff_5 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|0, exact #b|1 |] ==> inl State_1_suff_6 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1 |] ==> inl State_1_suff_7 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0 |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0 |] ==> inl State_1_suff_10 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|0, exact #b|1 |] ==> inl State_1_suff_11 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1 |] ==> inl State_1_suff_12 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      reject
    }}
  |}
  | State_1_suff_3 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_3;
  |}
  | State_1_suff_5 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_5;
  |}
  | State_1_suff_6 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_6;
  |}
  | State_1_suff_7 => {|
    st_op := extract(buf_48);
    st_trans := transition inl State_7;
  |}
  | State_1_suff_10 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_10;
  |}
  | State_1_suff_11 => {|
    st_op := extract(buf_16);
    st_trans := transition inl State_11;
  |}
  | State_1_suff_12 => {|
    st_op := extract(buf_48);
    st_trans := transition inl State_12;
  |}
  | State_2 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_0 ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_1 ;;;
      [| exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_2_suff_3 ;;;
      reject
    }}
  |}
  | State_2_suff_0 => {|
    st_op := extract(buf_352);
    st_trans := transition inl State_0;
  |}
  | State_2_suff_1 => {|
    st_op := extract(buf_320);
    st_trans := transition accept;
  |}
  | State_2_suff_2 => {|
    st_op := extract(buf_288);
    st_trans := transition accept;
  |}
  | State_2_suff_3 => {|
    st_op := extract(buf_256);
    st_trans := transition accept;
  |}
  | State_3 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_0 ;;;
      [| exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_3_suff_1 ;;;
      reject
    }}
  |}
  | State_3_suff_0 => {|
    st_op := extract(buf_48);
    st_trans := transition accept;
  |}
  | State_3_suff_1 => {|
    st_op := extract(buf_80);
    st_trans := transition accept;
  |}
  | State_4 => {|
    st_op := extract(buf_40);
    st_trans := transition select (| (EHdr buf_40)[15 -- 15], (EHdr buf_40)[14 -- 14], (EHdr buf_40)[13 -- 13], (EHdr buf_40)[12 -- 12], (EHdr buf_40)[11 -- 11], (EHdr buf_40)[10 -- 10], (EHdr buf_40)[9 -- 9], (EHdr buf_40)[8 -- 8], (EHdr buf_40)[7 -- 7], (EHdr buf_40)[6 -- 6], (EHdr buf_40)[5 -- 5], (EHdr buf_40)[4 -- 4], (EHdr buf_40)[3 -- 3], (EHdr buf_40)[2 -- 2], (EHdr buf_40)[1 -- 1], (EHdr buf_40)[0 -- 0], (EHdr buf_40)[39 -- 39], (EHdr buf_40)[38 -- 38], (EHdr buf_40)[37 -- 37], (EHdr buf_40)[36 -- 36], (EHdr buf_40)[35 -- 35], (EHdr buf_40)[34 -- 34], (EHdr buf_40)[33 -- 33], (EHdr buf_40)[32 -- 32], (EHdr buf_40)[31 -- 31], (EHdr buf_40)[30 -- 30], (EHdr buf_40)[29 -- 29], (EHdr buf_40)[28 -- 28], (EHdr buf_40)[27 -- 27], (EHdr buf_40)[26 -- 26], (EHdr buf_40)[25 -- 25], (EHdr buf_40)[24 -- 24]|) {{
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_4_suff_0 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_4_suff_1 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_4_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_4_suff_3 ;;;
      reject
    }}
  |}
  | State_4_suff_0 => {|
    st_op := extract(buf_104);
    st_trans := transition accept;
  |}
  | State_4_suff_1 => {|
    st_op := extract(buf_168);
    st_trans := transition inl State_1;
  |}
  | State_4_suff_2 => {|
    st_op := extract(buf_136);
    st_trans := transition accept;
  |}
  | State_4_suff_3 => {|
    st_op := extract(buf_72);
    st_trans := transition accept;
  |}
  | State_5 => {|
    st_op := extract(buf_40);
    st_trans := transition select (| (EHdr buf_40)[15 -- 15], (EHdr buf_40)[14 -- 14], (EHdr buf_40)[13 -- 13], (EHdr buf_40)[12 -- 12], (EHdr buf_40)[11 -- 11], (EHdr buf_40)[10 -- 10], (EHdr buf_40)[9 -- 9], (EHdr buf_40)[8 -- 8], (EHdr buf_40)[7 -- 7], (EHdr buf_40)[6 -- 6], (EHdr buf_40)[5 -- 5], (EHdr buf_40)[4 -- 4], (EHdr buf_40)[3 -- 3], (EHdr buf_40)[2 -- 2], (EHdr buf_40)[1 -- 1], (EHdr buf_40)[0 -- 0], (EHdr buf_40)[39 -- 39], (EHdr buf_40)[38 -- 38], (EHdr buf_40)[37 -- 37], (EHdr buf_40)[36 -- 36], (EHdr buf_40)[35 -- 35], (EHdr buf_40)[34 -- 34], (EHdr buf_40)[33 -- 33], (EHdr buf_40)[32 -- 32], (EHdr buf_40)[31 -- 31], (EHdr buf_40)[30 -- 30], (EHdr buf_40)[29 -- 29], (EHdr buf_40)[28 -- 28], (EHdr buf_40)[27 -- 27], (EHdr buf_40)[26 -- 26], (EHdr buf_40)[25 -- 25], (EHdr buf_40)[24 -- 24]|) {{
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_5_suff_0 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_5_suff_1 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_5_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_5_suff_3 ;;;
      reject
    }}
  |}
  | State_5_suff_0 => {|
    st_op := extract(buf_136);
    st_trans := transition accept;
  |}
  | State_5_suff_1 => {|
    st_op := extract(buf_200);
    st_trans := transition inl State_1;
  |}
  | State_5_suff_2 => {|
    st_op := extract(buf_168);
    st_trans := transition accept;
  |}
  | State_5_suff_3 => {|
    st_op := extract(buf_104);
    st_trans := transition accept;
  |}
  | State_6 => {|
    st_op := extract(buf_40);
    st_trans := transition select (| (EHdr buf_40)[15 -- 15], (EHdr buf_40)[14 -- 14], (EHdr buf_40)[13 -- 13], (EHdr buf_40)[12 -- 12], (EHdr buf_40)[11 -- 11], (EHdr buf_40)[10 -- 10], (EHdr buf_40)[9 -- 9], (EHdr buf_40)[8 -- 8], (EHdr buf_40)[7 -- 7], (EHdr buf_40)[6 -- 6], (EHdr buf_40)[5 -- 5], (EHdr buf_40)[4 -- 4], (EHdr buf_40)[3 -- 3], (EHdr buf_40)[2 -- 2], (EHdr buf_40)[1 -- 1], (EHdr buf_40)[0 -- 0], (EHdr buf_40)[39 -- 39], (EHdr buf_40)[38 -- 38], (EHdr buf_40)[37 -- 37], (EHdr buf_40)[36 -- 36], (EHdr buf_40)[35 -- 35], (EHdr buf_40)[34 -- 34], (EHdr buf_40)[33 -- 33], (EHdr buf_40)[32 -- 32], (EHdr buf_40)[31 -- 31], (EHdr buf_40)[30 -- 30], (EHdr buf_40)[29 -- 29], (EHdr buf_40)[28 -- 28], (EHdr buf_40)[27 -- 27], (EHdr buf_40)[26 -- 26], (EHdr buf_40)[25 -- 25], (EHdr buf_40)[24 -- 24]|) {{
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_6_suff_0 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_6_suff_1 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_6_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_6_suff_3 ;;;
      reject
    }}
  |}
  | State_6_suff_0 => {|
    st_op := extract(buf_168);
    st_trans := transition accept;
  |}
  | State_6_suff_1 => {|
    st_op := extract(buf_232);
    st_trans := transition inl State_1;
  |}
  | State_6_suff_2 => {|
    st_op := extract(buf_200);
    st_trans := transition accept;
  |}
  | State_6_suff_3 => {|
    st_op := extract(buf_136);
    st_trans := transition accept;
  |}
  | State_7 => {|
    st_op := extract(buf_40);
    st_trans := transition select (| (EHdr buf_40)[15 -- 15], (EHdr buf_40)[14 -- 14], (EHdr buf_40)[13 -- 13], (EHdr buf_40)[12 -- 12], (EHdr buf_40)[11 -- 11], (EHdr buf_40)[10 -- 10], (EHdr buf_40)[9 -- 9], (EHdr buf_40)[8 -- 8], (EHdr buf_40)[7 -- 7], (EHdr buf_40)[6 -- 6], (EHdr buf_40)[5 -- 5], (EHdr buf_40)[4 -- 4], (EHdr buf_40)[3 -- 3], (EHdr buf_40)[2 -- 2], (EHdr buf_40)[1 -- 1], (EHdr buf_40)[0 -- 0], (EHdr buf_40)[39 -- 39], (EHdr buf_40)[38 -- 38], (EHdr buf_40)[37 -- 37], (EHdr buf_40)[36 -- 36], (EHdr buf_40)[35 -- 35], (EHdr buf_40)[34 -- 34], (EHdr buf_40)[33 -- 33], (EHdr buf_40)[32 -- 32], (EHdr buf_40)[31 -- 31], (EHdr buf_40)[30 -- 30], (EHdr buf_40)[29 -- 29], (EHdr buf_40)[28 -- 28], (EHdr buf_40)[27 -- 27], (EHdr buf_40)[26 -- 26], (EHdr buf_40)[25 -- 25], (EHdr buf_40)[24 -- 24]|) {{
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_7_suff_0 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_7_suff_1 ;;;
      [| *, *, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_7_suff_2 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_7_suff_3 ;;;
      reject
    }}
  |}
  | State_7_suff_0 => {|
    st_op := extract(buf_200);
    st_trans := transition accept;
  |}
  | State_7_suff_1 => {|
    st_op := extract(buf_264);
    st_trans := transition inl State_1;
  |}
  | State_7_suff_2 => {|
    st_op := extract(buf_232);
    st_trans := transition accept;
  |}
  | State_7_suff_3 => {|
    st_op := extract(buf_168);
    st_trans := transition accept;
  |}
  | State_8 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_8_suff_0 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_8_suff_1 ;;;
      [| *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_8_suff_2 ;;;
      [| *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_8_suff_3 ;;;
      reject
    }}
  |}
  | State_8_suff_0 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_0;
  |}
  | State_8_suff_1 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_1;
  |}
  | State_8_suff_2 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_2;
  |}
  | State_8_suff_3 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_3;
  |}
  | State_9 => {|
    st_op := extract(buf_32);
    st_trans := transition select (| (EHdr buf_32)[15 -- 15], (EHdr buf_32)[14 -- 14], (EHdr buf_32)[13 -- 13], (EHdr buf_32)[12 -- 12], (EHdr buf_32)[11 -- 11], (EHdr buf_32)[10 -- 10], (EHdr buf_32)[9 -- 9], (EHdr buf_32)[8 -- 8], (EHdr buf_32)[7 -- 7], (EHdr buf_32)[6 -- 6], (EHdr buf_32)[5 -- 5], (EHdr buf_32)[4 -- 4], (EHdr buf_32)[3 -- 3], (EHdr buf_32)[2 -- 2], (EHdr buf_32)[1 -- 1], (EHdr buf_32)[0 -- 0], (EHdr buf_32)[31 -- 31], (EHdr buf_32)[30 -- 30], (EHdr buf_32)[29 -- 29], (EHdr buf_32)[28 -- 28], (EHdr buf_32)[27 -- 27], (EHdr buf_32)[26 -- 26], (EHdr buf_32)[25 -- 25], (EHdr buf_32)[24 -- 24], (EHdr buf_32)[23 -- 23], (EHdr buf_32)[22 -- 22], (EHdr buf_32)[21 -- 21], (EHdr buf_32)[20 -- 20], (EHdr buf_32)[19 -- 19], (EHdr buf_32)[18 -- 18], (EHdr buf_32)[17 -- 17], (EHdr buf_32)[16 -- 16]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_9_suff_0 ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_9_suff_1 ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, exact #b|0, exact #b|1, exact #b|1, exact #b|1, *, *, *, *, *, *, *, * |] ==> inl State_9_suff_2 ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, exact #b|1, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, * |] ==> inl State_9_suff_3 ;;;
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|0, exact #b|1, exact #b|1, exact #b|1, exact #b|0, exact #b|1, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_9_suff_6 ;;;
      [| exact #b|1, exact #b|0, exact #b|0, *, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| exact #b|1, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|1, *, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> accept ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> reject ;;;
      reject
    }}
  |}
  | State_9_suff_0 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_0;
  |}
  | State_9_suff_1 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_1;
  |}
  | State_9_suff_2 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_2;
  |}
  | State_9_suff_3 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_3;
  |}
  | State_9_suff_6 => {|
    st_op := extract(buf_32);
    st_trans := transition inl State_6;
  |}
  | State_10 => {|
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0], (EHdr buf_16)[15 -- 15], (EHdr buf_16)[14 -- 14], (EHdr buf_16)[13 -- 13], (EHdr buf_16)[12 -- 12], (EHdr buf_16)[11 -- 11], (EHdr buf_16)[10 -- 10], (EHdr buf_16)[9 -- 9], (EHdr buf_16)[8 -- 8], (EHdr buf_16)[7 -- 7], (EHdr buf_16)[6 -- 6], (EHdr buf_16)[5 -- 5], (EHdr buf_16)[4 -- 4], (EHdr buf_16)[3 -- 3], (EHdr buf_16)[2 -- 2], (EHdr buf_16)[1 -- 1], (EHdr buf_16)[0 -- 0]|) {{
      [| exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|1, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, exact #b|0, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_10_suff_0 ;;;
      [| *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, *, * |] ==> inl State_10_suff_1 ;;;
      reject
    }}
  |}
  | State_10_suff_0 => {|
    st_op := extract(buf_192);
    st_trans := transition accept;
  |}
  | State_10_suff_1 => {|
    st_op := extract(buf_32);
    st_trans := transition accept;
  |}
end.
Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).
End Optimized. *)
