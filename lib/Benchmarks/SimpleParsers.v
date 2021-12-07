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

Module ParseOne.
  Inductive state :=
  | Start.
  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
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
  | Bit : header 1.

  Derive Signature for header.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ Bit Bit := left eq_refl ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [1].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bit] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
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
    | Start =>
      {| st_op := extract(Bit);
         st_trans := transition select (| EHdr Bit |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ParseOne.

Module ParseZero.
  Inductive state :=
  | Start.
  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
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
  | Bit : header 1.

  Derive Signature for header.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ Bit Bit := left eq_refl ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [1].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bit] |}.
  Next Obligation.
    repeat constructor;
    unfold "~";
    intros;
    destruct H;
    now inversion H || now inversion H0.
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
    | Start =>
      {| st_op := extract(Bit);
         st_trans := transition select (| EHdr Bit |) {{
           [| exact #b|0 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End ParseZero.

Module OneZero.
  Definition state: Type := ParseOne.state + ParseZero.state.
  Global Instance state_eq_dec: EquivDec.EqDec state eq :=
    ltac:(typeclasses eauto).

  Definition header := Sum.H ParseOne.header ParseZero.header.
  Global Instance header_eq_dec': EquivDec.EqDec (H' header) eq.
  Proof.
    eapply Sum.H'_eq_dec; typeclasses eauto.
  Defined.

  Global Instance header_eq_dec: forall n, EquivDec.EqDec (header n) eq.
  Proof.
    typeclasses eauto.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ (header_eq_dec n).
  Proof.
    typeclasses eauto.
  Defined.

  Global Instance header_finite': @Finite {n & header n} _ header_eq_dec'.
  econstructor.
  - eapply Sum.H_finite.
  - intros.
    simpl.
    destruct x.
    inversion h;
    dependent destruction H;
    dependent destruction h;
    dependent destruction h;
    repeat (
      match goal with
      | |- ?L \/ ?R => (now left; trivial) || right
      end
    ).
  Defined.

  Definition aut := Sum.sum ParseOne.aut ParseZero.aut.
End OneZero.


Module TwoOnesChunk.
  Inductive state :=
  | Start.
  Equations state_eq_dec (l: state) (r: state) : {l = r} + {l <> r} :=
  { state_eq_dec Start Start := left eq_refl }.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start] |}.
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
  | Bits : header 2.

  Derive Signature for header.

  Equations header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y} :=
  {
    header_eqdec_ _ Bits Bits := left eq_refl ;
  }.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [2].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bits] |}.
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
    | Start =>
      {| st_op := extract(Bits);
         st_trans := transition select (| EHdr Bits |) {{
           [| exact #b|1|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TwoOnesChunk.

Module TwoOnesBucket.
  Inductive state :=
  | Start
  | Next.

  Scheme Equality for state.

  Global Instance state_eqdec: EquivDec.EqDec state eq := state_eq_dec.
  Global Program Instance state_finite: @Finite state _ state_eq_dec :=
    {| enum := [Start; Next] |}.
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
  | Bits : header 2
  | Val : header 1.

  Derive Signature for header.

  Definition h1_eq_dec (x y: header 1) : {x = y} + {x <> y} :=
    match x, y with
    | Val, Val => left eq_refl
    | _, _ => idProp
    end.
  Definition h2_eq_dec (x y: header 2) : {x = y} + {x <> y} :=
    match x, y with
    | Bits, Bits => left eq_refl
    | _, _ => idProp
    end.

  Definition header_eqdec_ (n: nat) (x: header n) (y: header n) : {x = y} + {x <> y}.
    solve_header_eqdec_ n x y
      ((existT (fun n => forall x y: header n, {x = y} + {x <> y}) 1 h1_eq_dec) :: (existT _ 2 h2_eq_dec) :: nil).
  Defined.

  Global Instance header_eqdec: forall n, EquivDec.EqDec (header n) eq := header_eqdec_.

  Global Instance header_eqdec': EquivDec.EqDec (Syntax.H' header) eq.
  Proof.
    solve_eqdec'.
  Defined.

  Global Instance header_finite: forall n, @Finite (header n) _ _.
  Proof.
    intros n; solve_indexed_finiteness n [2; 1].
  Qed.

  Global Program Instance header_finite': @Finite {n & header n} _ header_eqdec' :=
    {| enum := [ existT _ _ Bits; existT _ _ Val] |}.
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
    | Start =>
      {| st_op :=
          extract(Val) ;;
          Bits <- EConcat (m := 1) (EHdr Val) ((EHdr Bits)[1--1]) ;
         st_trans := transition select (| EHdr Val |) {{
           [| exact #b|1 |] ==> inl Next ;;;
            @reject state
         }}
      |}
    | Next =>
      {| st_op :=
          extract(Val) ;;
          Bits <- EConcat (m := 1) (ESlice (n := 2) (EHdr Bits) 0 0) (EHdr Val) ;
         st_trans := transition select (| EHdr Val |) {{
           [| exact #b|1 |] ==> accept ;;;
            @reject state
         }}
      |}
    end.

  Program Definition aut: Syntax.t state header :=
    {| t_states := states |}.
  Solve Obligations with (destruct s; cbv; Lia.lia).

End TwoOnesBucket.
