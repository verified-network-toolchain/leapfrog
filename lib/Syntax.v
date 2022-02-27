Require Coq.Lists.List.
Import List.ListNotations.
Require Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.
Require Import Equations.Prop.EqDecInstances.
Require Import Coq.Program.Program.
Require Import Leapfrog.HAList.
Require Import Leapfrog.FinType.
Require Import Leapfrog.Ntuple.
Require Leapfrog.DepEnv.
Require Leapfrog.P4automaton.
Module P4A := P4automaton.

Module Env := Leapfrog.DepEnv.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Open Scope list_scope.

Require Import Coq.Init.Logic.
Import EqNotations.

Section Syntax.

  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (St: Type).
  Context `{St_eq_dec: EquivDec.EqDec St eq}.
  Context `{St_finite: @Finite St _ St_eq_dec}.

  (* Typed header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.

  Variable (Hdr_sz: Hdr -> N).

  Inductive hdr_ref: Type :=
  | HRVar (var: Hdr).
  (*| HRField (hdr: hdr_ref) (field: string).*)
  Derive NoConfusion for hdr_ref.
  Global Program Instance hdr_ref_eq_dec : EquivDec.EqDec hdr_ref eq :=
    { equiv_dec x y :=
        match x, y with
        | @HRVar x, @HRVar y =>
          if x == y then in_left else in_right
        end }.
  Solve Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Inductive expr : N -> Type :=
  | EHdr (h: Hdr): expr (Hdr_sz h)
  | ELit {n} (bs: n_tuple bool n): expr n
  | ESlice {n} (e: expr n) (hi lo: N): expr (N.min (1 + hi) n - lo)
  | EConcat {n m} (l: expr n) (r: expr m): expr (n + m).
  (* todo: binops, ...? *)

  Definition state_ref: Type := St + bool.

  Inductive v n :=
  | VBits: n_tuple bool n -> v n.

  Global Program Instance v_eq_dec (n: N): EquivDec.EqDec (v n) eq :=
    { equiv_dec x y :=
        match x, y with
        | VBits xs, VBits ys =>
          if xs == ys
          then in_left
          else in_right
        end }.
  Solve All Obligations with unfold equiv, complement in *;
    program_simpl; congruence.

  Global Program Instance v_finite (n: N): Finite (v n) :=
    {| enum := List.map (@VBits n) (enum (n_tuple bool n)) |}.
  Next Obligation.
    apply NoDup_map.
    - intros x y Heq; inversion Heq; auto.
    - eapply NtupleProofs.BoolTupleFinite.
  Qed.
  Next Obligation.
    destruct x.
    rewrite List.in_map_iff.
    eexists; intuition eauto.
    eapply NtupleProofs.BoolTupleFinite.
  Qed.

  Inductive typ :=
  | TBits (n: N)
  | TPair (t1 t2: typ).
  Derive NoConfusion for typ.

  Inductive pat: typ -> Type :=
  | PExact {n} (val: v n) : pat (TBits n)
  | PAny: forall n, pat (TBits n)
  | PPair {t1 t2} (p1: pat t1) (p2: pat t2) : pat (TPair t1 t2).
  Derive Signature for pat.

  Inductive cond: typ -> Type :=
  | CExpr {n} (e: expr n) : cond (TBits n)
  | CPair {t1 t2} (c1: cond t1) (c2: cond t2) : cond (TPair t1 t2).
  Derive Signature for cond.

  Record sel_case t: Type :=
    { sc_pat: pat t;
      sc_st: state_ref }.

  Inductive transition: Type :=
  | TGoto (state: state_ref)
  | TSel {t} (c: cond t) (cases: list (sel_case t)) (default: state_ref).

  Inductive op :=
  | OpNil: op
  | OpSeq (o1 o2: op)
  | OpExtract (hdr: Hdr)
  | OpAsgn (lhs: Hdr) (rhs: expr (Hdr_sz lhs)).

  Fixpoint op_size (o: op) : N :=
    match o with
    | OpNil => 0
    | OpSeq o1 o2 => op_size o1 + op_size o2
    | OpExtract hdr => Hdr_sz hdr
    | @OpAsgn _ _ => 0
    end.

  Record state: Type :=
    { st_op: op;
      st_trans: transition }.

  Definition st_size (st: state) : N :=
    op_size (st_op st).

  Record t: Type :=
    { t_states: St -> state;
      t_nonempty: forall h, (Hdr_sz h > 0)%N;
      t_has_extract: forall s, (st_size (t_states s) > 0)%N }.

  Program Definition bind (s: St) (st: state) (ex: (st_size st > 0)%N) (ok: forall h, (Hdr_sz h > 0)%N) (a: t) :=
    {| t_states := fun s' => if s == s' then st else a.(t_states) s' |}.
  Next Obligation.
    destruct (s == s0).
    - auto.
    - eapply a.(t_has_extract).
  Qed.

  Definition size (a: t) (s: St) :=
    st_size (a.(t_states) s).

  

End Syntax.

Section Fmap.
  Set Implicit Arguments.
  Variables (St1 St2: Type).
  Variables (Hdr1 Hdr2: Type).
  Variable (sz1: Hdr1 -> N).
  Variable (sz2: Hdr2 -> N).
  Variable (f: St1 -> St2).
  Variable (g: Hdr1 -> Hdr2).

  Hypothesis g_sound: forall h, sz1 h = sz2 (g h).

  Definition hdr_ref_fmapH (h: hdr_ref Hdr1) : hdr_ref Hdr2 :=
    match h with
    | HRVar h => HRVar (g h)
    end.

  Equations expr_fmapH {n: N} (e: expr sz1 n) : expr sz2 n := {
    expr_fmapH (EHdr _ h) := eq_rect_r _ (EHdr _ (g h)) (g_sound h);
    expr_fmapH (ELit _ bs) := ELit _ bs;
    expr_fmapH (ESlice e hi lo) := ESlice (expr_fmapH e) hi lo;
    expr_fmapH (EConcat l r) := EConcat (expr_fmapH l) (expr_fmapH r)
  }.

  Definition state_ref_fmapS (s: state_ref St1) : state_ref St2 :=
    match s with
    | inl s' => inl (f s')
    | inr r => inr r
    end.

  Definition sel_case_fmapS {t} (c: sel_case St1 t) : sel_case St2 t :=
    {| sc_pat := c.(sc_pat);
       sc_st := state_ref_fmapS c.(sc_st) |}.

  Fixpoint cond_fmapH {t} (c: cond sz1 t) : cond sz2 t :=
    match c with
    | CExpr e => CExpr (expr_fmapH e)
    | CPair c1 c2 => CPair (cond_fmapH c1) (cond_fmapH c2)
    end.

  Definition transition_fmapSH (t: transition St1 sz1) : transition St2 sz2 :=
    match t with
    | TGoto _ s => TGoto _ (state_ref_fmapS s)
    | TSel cond cases default =>
      TSel (cond_fmapH cond) (List.map sel_case_fmapS cases) (state_ref_fmapS default)
    end.

  Equations op_fmapH (o: op sz1) : op sz2 := {
    op_fmapH OpNil := OpNil _;
    op_fmapH (OpSeq o1 o2) := OpSeq (op_fmapH o1) (op_fmapH o2);
    op_fmapH (OpExtract _ hdr) := OpExtract _ (g hdr);
    op_fmapH (OpAsgn lhs rhs) :=
      OpAsgn (g lhs) (eq_rect _ _ (expr_fmapH rhs) _ (g_sound lhs))
  }.

  Definition state_fmapSH (s: state St1 sz1) : state St2 sz2 :=
    {| st_op := op_fmapH s.(st_op);
       st_trans := transition_fmapSH s.(st_trans) |}.

  Lemma op_fmapH_size :
    forall o,
      op_size (op_fmapH o) = op_size o.
  Proof.
    induction o; autorewrite with op_fmapH; simpl; congruence.
  Qed.

  Lemma state_fmapSH_size :
    forall s,
      st_size (state_fmapSH s) = st_size s.
  Proof.
    unfold st_size.
    now setoid_rewrite op_fmapH_size.
  Qed.

End Fmap.

Section Interp.
  Unset Implicit Arguments.
  (* State identifiers. *)
  Variable (St: Type).
  Context `{St_eqdec: EquivDec.EqDec St eq}.

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.
  Variable (Hdr_sz: Hdr -> N).
  Variable (a: t St Hdr_sz).

  Definition store := Env.t Hdr (fun h => v (Hdr_sz h)).

  Definition clamp_list (n: N) (l: list bool) :=
    List.firstn (N.to_nat n) (l ++ (List.repeat false (List.length l - (N.to_nat n)))).

  Definition assign (h: Hdr) (v: v (Hdr_sz h)) (st: store) : store :=
    Env.bind _ _ h v st.

  Definition find (h: Hdr) (st: store) : v (Hdr_sz h) :=
    Env.get _ _ h st.

  Lemma assign_find:
    forall (h: Hdr) v s,
      find h (assign h v s) = v.
  Proof.
    intros.
    unfold find, assign.
    unfold Env.bind, Env.get.
    generalize (elem_of_enum h).
    intros.
    unfold store in s.
    unfold Env.t in s.
    induction (enum Hdr).
    contradiction.
    dependent destruction s.
    autorewrite with bind.
    destruct (Hdr_eq_dec _ _).
    autorewrite with get.
    destruct (Hdr_eq_dec _ _).
    unfold equiv in *.
    dependent destruction e0.
    now dependent destruction e.
    simpl.
    destruct i.
    contradiction.
    contradiction.
    simpl.
    destruct i.
    unfold equiv, complement in c.
    exfalso.
    symmetry in e.
    contradiction.
    autorewrite with get.
    destruct (Hdr_eq_dec _ _).
    contradiction.
    simpl.
    apply IHl.
  Qed.

  Lemma find_not_first:
    forall h1 h2 v s,
      h1 <> h2 ->
      find h1 (assign h2 v s) =
      find h1 s.
  Proof.
    intros.
    unfold assign.
    unfold Env.bind.
    unfold find.
    unfold Env.get.
    generalize (elem_of_enum h1).
    generalize (elem_of_enum h2).
    intros.
    unfold store in s.
    unfold Env.t in s.
    induction (enum Hdr).
    - contradiction.
    - dependent destruction s.
      autorewrite with get.
      autorewrite with bind.
      destruct (Hdr_eq_dec _ _).
      autorewrite with get.
      destruct (Hdr_eq_dec _ _).
      exfalso.
      unfold equiv, complement in *.
      congruence.
      congruence.
      simpl.
      autorewrite with get.
      destruct (Hdr_eq_dec _ _).
      reflexivity.
      simpl.
      destruct i0.
      congruence.
      destruct i.
      congruence.
      apply IHl.
  Qed.

  Lemma to_nat_float_1:
    forall hi e0 lo, 
      (Nat.min (1 + N.to_nat hi) (N.to_nat e0) - N.to_nat lo) = 
      N.to_nat (N.min (1 + hi) e0 - lo).
  Proof.
    intros.
    erewrite N2Nat.inj_sub.
    erewrite N2Nat.inj_min.
    erewrite N2Nat.inj_add.
    trivial.
  Qed.
  Local Obligation Tactic := intros.
  Equations eval_expr (n: N) (st: store) (e: expr Hdr_sz n) : v n :=
    { eval_expr n st (EHdr n h) := find h st;
      eval_expr n st (ELit _ bs) := VBits bs;
      eval_expr n st (ESlice e hi lo) :=
        let '(VBits bs) := eval_expr _ st e in
        VBits (n_tuple_slice hi lo bs);
      eval_expr n st (EConcat l r) :=
        let '(VBits bs_l) := eval_expr _ st l in
        let '(VBits bs_r) := eval_expr _ st r in
        VBits (n_tuple_concat bs_l bs_r)
    }.

  Equations eval_op (st: store) (o: op Hdr_sz) (bits: n_tuple bool (op_size o))  : store :=
    {
      eval_op st (OpNil _) bits :=
        st;
      eval_op st (@OpExtract hdr) bits :=
        assign hdr (VBits bits) st;
      eval_op st (OpSeq o1 o2) bits :=
        let bits' := n_tuple_take_n (op_size o1) bits in
        let st := eval_op st o1 (rewrite_size _ bits') in
        eval_op st o2 (rewrite_size _ (n_tuple_skip_n (op_size o1) bits));
      eval_op st (OpAsgn hdr expr) bits :=
        assign hdr (eval_expr _ st expr) st
    }.
  Next Obligation.
    simpl op_size.
    Lia.lia.
  Qed.
  Next Obligation.
    simpl op_size.
    Lia.lia.
  Qed.

  Program Definition update
    (state: St)
    (bits: n_tuple bool (st_size (t_states a state)))
    (st: store)
    : store :=
    eval_op st
            (* Deal with conversion of n-tuple to (n+0)-tuple *)
            (a.(t_states) state).(st_op)
            (eq_rect _ _ bits _ (N.add_0_l _)).

  Equations match_pat {T: typ} (st: store) (c: cond Hdr_sz T) (p: pat T) : bool := {
    match_pat st (CExpr e) (PExact val) :=
      if eval_expr _ st e == val then true else false;
    match_pat st (CExpr e) (PAny _) :=
      true;
    match_pat st (CPair c1 c2) (PPair p1 p2) =>
      andb (match_pat st c1 p1) (match_pat st c2 p2)
  }.

  Fixpoint eval_sel
    {T: typ}
    (st: store)
    (c: cond Hdr_sz T)
    (cases: list (sel_case St T))
    (default: state_ref St)
    : state_ref St :=
    match cases with
    | sc::cases =>
      if match_pat st c sc.(sc_pat)
      then sc.(sc_st)
      else eval_sel st c cases default
    | nil => default
    end.

  Definition eval_trans (st: store) (t: transition St Hdr_sz) : state_ref St :=
    match t with
    | TGoto _ state => state
    | TSel cond cases default =>
      eval_sel st cond cases default
    end.

  Definition transitions (s: St) (st: store) : state_ref St :=
    eval_trans st (a.(t_states) s).(st_trans).

  Definition possible_next_states (st: state St Hdr_sz) : list (state_ref St) :=
    match st.(st_trans) with
    | TGoto _ s' =>
      [s']
    | TSel _ cases default =>
      default :: List.map (fun c => sc_st c) cases
    end.

  Program Definition interp : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := St;
       P4A.size := (size a);
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := _ |}.
  Next Obligation.
    pose proof a.(t_has_extract).
    unfold t_states in H.
    simpl in H.
    unfold size.
    specialize (H s).
    destruct a.
    simpl in *.
    Lia.lia.
  Defined.
End Interp.
Arguments EHdr {_ _} _.
Arguments ELit {_ _} _.
Arguments ESlice {_ _} _ _ _.
Arguments interp {_ _ _ _ _ _} a.


Section Properties.

  (* State identifiers. *)
  Variable (St1: Type).
  Context `{St1_eq_dec: EquivDec.EqDec St1 eq}.
  Context `{St1_finite: @Finite St1 _ St1_eq_dec}.

  Variable (St2: Type).
  Context `{St2_eq_dec: EquivDec.EqDec St2 eq}.
  Context `{St2_finite: @Finite St2 _ St2_eq_dec}.

  Notation St := ((St1 + St2)%type).

  (* Header identifiers. *)
  Variable (Hdr: Type).
  Variable (Hdr_sz: Hdr -> N).
  Context `{Hdr_eq_dec: EquivDec.EqDec Hdr eq}.
  Context `{Hdr_finite: @Finite Hdr _ Hdr_eq_dec}.

  Variable (a: t St Hdr_sz).

  Import P4A.

  Lemma conf_state_step_transition_syntactic
    (q: P4A.configuration (interp a))
    (b: bool)
    (s: St)
  :
    conf_state q = inl s ->
    (1 + conf_buf_len q = size' (interp a) (conf_state q))%N ->
    List.In (conf_state (step q b))
            (possible_next_states _ _ _ (t_states a s)).
  Proof.
  Admitted.
    (* intros.
    rewrite conf_state_step_transition with (Heq := H0).
    destruct (conf_state q); [|discriminate].
    autorewrite with update'.
    autorewrite with transitions'.
    simpl.
    unfold Syntax.transitions.
    unfold Syntax.eval_trans.
    inversion H; subst.
    unfold possible_next_states.
    destruct (st_trans _).
    - apply List.in_eq.
    - induction cases.
      + simpl; now left.
      + simpl eval_sel.
        rewrite List.map_cons.
        destruct (match_pat _ _ _ _).
        * apply List.in_cons.
          apply List.in_eq.
        * destruct IHcases.
          -- rewrite H1 at 2.
             apply List.in_eq.
          -- now repeat apply List.in_cons.
  Qed. *)

  Lemma conf_state_follow_transition_syntactic
    (q: configuration (interp a))
    (bs: list bool)
    (s: St)
  :
    conf_state q = inl s ->
    ((N.of_nat (length bs)) + conf_buf_len q = size' (interp a) (conf_state q))%N ->
    List.In (conf_state (follow q bs))
            (possible_next_states _ _ _ (t_states a s)).
  Proof.
    revert q; induction bs; intros.
    - simpl in H0.
      pose proof (conf_buf_sane q).
      Lia.lia.
    - destruct bs; simpl in *.
      + autorewrite with follow.
        now apply conf_state_step_transition_syntactic.
      + rewrite follow_equation_2.
        apply IHbs.
        * rewrite conf_state_step_fill; auto. 
          destruct (conf_buf_len q); simpl; Lia.lia.
        * rewrite conf_buf_len_step_fill; 
          try now (
            destruct (conf_buf_len q); simpl; Lia.lia
          ).
          rewrite conf_state_step_fill; try now (
            destruct (conf_buf_len q); simpl; Lia.lia
          ).
  Qed.

End Properties.
