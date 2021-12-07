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
  Notation eth_size := 112.
  Notation mpls_size := 32.
  Notation eompls_size := 28.
  Notation ipv4_size := 156.
  Notation ipv6_size := 316.
  Notation ipv4_size_5 := 152.
  Notation ipv4_size_6 := 184.
  Notation ipv4_size_7 := 216.
  Notation ipv4_size_8 := 248.

  Inductive header: nat -> Type :=
  | HdrEth0: header eth_size
  | HdrEth1: header eth_size
  | HdrMPLS0: header mpls_size
  | HdrMPLS1: header mpls_size
  | HdrEoMPLS: header eompls_size
  | HdrIPVer: header 4
  | HdrIPv4_5: header ipv4_size_5
  | HdrIPv4_6: header ipv4_size_6
  | HdrIPv4_7: header ipv4_size_7
  | HdrIPv4_8: header ipv4_size_8
  | HdrIPv6: header ipv6_size.

  Derive Signature for header.
  Definition h32_eq_dec (x y: header 32) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrMPLS0 =>
      match y with
      | HdrMPLS0 => left eq_refl
      | HdrMPLS1 => right _
      end
    | HdrMPLS1 =>
      match y with
      | HdrMPLS0 => right _
      | HdrMPLS1 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h4_eq_dec (x y: header 4) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPVer =>
      match y with
      | HdrIPVer => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h28_eq_dec (x y: header 28) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrEoMPLS =>
      match y with
      | HdrEoMPLS => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrEth0 =>
      match y with
      | HdrEth0 => left eq_refl
      | HdrEth1 => right _
      end
    | HdrEth1 =>
      match y with
      | HdrEth0 => right _
      | HdrEth1 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h316_eq_dec (x y: header 316) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv6 =>
      match y with
      | HdrIPv6 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h152_eq_dec (x y: header 152) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv4_5 =>
      match y with
      | HdrIPv4_5 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h184_eq_dec (x y: header 184) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv4_6 =>
      match y with
      | HdrIPv4_6 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h216_eq_dec (x y: header 216) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv4_7 =>
      match y with
      | HdrIPv4_7 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition h248_eq_dec (x y: header 248) : {x = y} + {x <> y}.
  refine (
    match x with
    | HdrIPv4_8 =>
      match y with
      | HdrIPv4_8 => left eq_refl
      end
    end
  ); unfold "<>"; intros H; inversion H.
  Defined.
  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h32_eq_dec) ::
      (existT _ _ h4_eq_dec) ::
      (existT _ _ h112_eq_dec) ::
      (existT _ _ h316_eq_dec) ::
      (existT _ _ h152_eq_dec) ::
      (existT _ _ h184_eq_dec) ::
      (existT _ _ h216_eq_dec) ::
      (existT _ _ h248_eq_dec) ::
      (existT _ _ h28_eq_dec) ::
        nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
    solve_eqdec'.
  Defined.
  Global Instance header_finite: forall n, @Finite (header n) _ _.
    intros n; solve_indexed_finiteness n [32; 4 ; 112 ; 316 ; 152; 184; 216; 248; 28 ].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [
        existT _ _ HdrEth0
      ; existT _ _ HdrEth1
      ; existT _ _ HdrMPLS0
      ; existT _ _ HdrMPLS1
      ; existT _ _ HdrEoMPLS
      ; existT _ _ HdrIPVer
      ; existT _ _ HdrIPv4_5
      ; existT _ _ HdrIPv4_6
      ; existT _ _ HdrIPv4_7
      ; existT _ _ HdrIPv4_8
      ; existT _ _ HdrIPv6
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

  Definition states (s: state) : P4A.state state header :=
    match s with
    | ParseEth0 =>
      {| st_op := extract(HdrEth0);
        st_trans := transition select (| (EHdr HdrEth0)[111--96] |)
                                {{[| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|0|1|1|1 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|1|0|0|0|1|0|0|0|0|1|0|0|1|0|0|0 |] ==> inl ParseMPLS0 ;;;
                                  [| exact #b|0|0|0|0|1|0|0|0|0|0|0|0|0|0|0|0 |] ==> inl IgnoreIPVer4 ;;;
                                  [| exact #b|1|0|0|0|0|1|1|0|1|1|0|1|1|1|0|1 |] ==> inl IgnoreIPVer6 ;;;
                                  accept }}
      |}
    | ParseMPLS0 => 
      {| st_op := extract(HdrMPLS0);
        st_trans := transition select (| (EHdr HdrMPLS0)[23--23] |)
                                {{ [| hexact 0 |] ==> inl ParseMPLS1 ;;;
                                  [| hexact 1 |] ==> inl ParseIPVer ;;;
                                  reject
                                }}
      |}
    | ParseMPLS1 => 
      {| st_op := extract(HdrMPLS1);
        st_trans := transition select (| (EHdr HdrMPLS1)[23--23] |)
                              {{ [| hexact 1 |] ==> inl ParseIPVer ;;;
                                reject
                              }}
      |}
    | ParseIPVer =>
      {| st_op := extract(HdrIPVer);
        st_trans := transition select (| EHdr HdrIPVer |)
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
        st_trans := transition select (| EHdr HdrIPVer |) 
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



  Scheme Equality for state.
  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [ParseEth0; ParseEth1; ParseMPLS0; ParseMPLS1; ParseEoMPLS; ParseIPVer; ParseIPv4; ParseIPv6; ParseIPv4_5; ParseIPv4_6; ParseIPv4_7; ParseIPv4_8; IgnoreIPVer4; IgnoreIPVer6] |}.
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

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).
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
Global Program Instance state_finite: @Finite state _ state_eq_dec :=
  {| enum := [State_0; State_1; State_1_suff_0; State_0_suff_3; State_3_suff_1; State_4; State_2_suff_0; State_3; State_3_suff_2; State_0_suff_2; State_2; State_3_suff_3; State_3_suff_0; State_0_suff_1; State_4_trailer ; State_4_skip] |}.
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
| buf_320: header 320
| buf_128: header 128
| buf_64: header 64
| buf_112: header 112
| buf_16: header 16
| buf_32: header 32
| buf_304: header 304
| buf_240: header 240
| buf_144: header 144
| buf_176: header 176
| buf_208: header 208.
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
Definition h64_eq_dec (x y: header 64) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_64 =>
    match y with
    | buf_64 => left eq_refl
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
Definition h128_eq_dec (x y: header 128) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_128 =>
    match y with
    | buf_128 => left eq_refl
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
Definition h112_eq_dec (x y: header 112) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_112 =>
    match y with
    | buf_112 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h304_eq_dec (x y: header 304) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_304 =>
    match y with
    | buf_304 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h240_eq_dec (x y: header 240) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_240 =>
    match y with
    | buf_240 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h144_eq_dec (x y: header 144) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_144 =>
    match y with
    | buf_144 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h176_eq_dec (x y: header 176) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_176 =>
    match y with
    | buf_176 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Definition h208_eq_dec (x y: header 208) : {x = y} + {x <> y}.
refine (
  match x with
  | buf_208 =>
    match y with
    | buf_208 => left eq_refl
    end
  end
); unfold "<>"; intros H; inversion H.
Defined.
Derive Signature for header.
Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
  solve_header_eqdec_ n x y
    ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) _ h320_eq_dec) ::
     (existT _ _ h64_eq_dec) ::
     (existT _ _ h128_eq_dec) ::
     (existT _ _ h16_eq_dec) ::
     (existT _ _ h112_eq_dec) ::
     (existT _ _ h32_eq_dec) ::
     (existT _ _ h304_eq_dec) ::
     (existT _ _ h240_eq_dec) ::
     (existT _ _ h144_eq_dec) ::
     (existT _ _ h176_eq_dec) ::
     (existT _ _ h208_eq_dec) ::
      nil).
Defined.

Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.
Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  solve_eqdec'.
Defined.
Global Instance header_finite: forall n, @Finite (header n) _ _.
  intros n; solve_indexed_finiteness n [320; 64; 32 ; 128 ; 16 ; 112 ; 304 ; 240 ; 144 ; 176 ; 208 ].
Qed.

Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
  {| enum := [
      existT _ _ buf_320
    ; existT _ _ buf_128
    ; existT _ _ buf_64
    ; existT _ _ buf_112
    ; existT _ _ buf_16
    ; existT _ _ buf_32
    ; existT _ _ buf_304
    ; existT _ _ buf_240
    ; existT _ _ buf_144
    ; existT _ _ buf_176
    ; existT _ _ buf_208
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
    st_op := extract(buf_112);
    st_trans := transition select (| (EHdr buf_112)[111 -- 96] |) {{
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
    st_trans := transition select (| (EHdr buf_16)[7--4]|) {{
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
    st_trans := transition select (| (EHdr buf_16)[7 -- 7] |) {{
      [| exact #b|0 |] ==> inl State_4_skip ;;;
      [| exact #b|1 |] ==> inl State_4_trailer ;;;
      reject
    }}
  |}

  | State_4_skip => {| 
    st_op := extract(buf_32);
    st_trans := transition select (| (EHdr buf_32)[23 -- 23] |) {{
      [| exact #b|1 |] ==> inl State_4_trailer ;;;
      reject
    }}
  |}

  | State_4_trailer => {| 
    st_op := extract(buf_16);
    st_trans := transition select (| (EHdr buf_16)[3 -- 0], (EHdr buf_16)[7--4] |) {{
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
Program Definition aut: Syntax.t state header :=
  {| t_states := states |}.
Solve Obligations with (destruct s; cbv; Lia.lia).
End Optimized.