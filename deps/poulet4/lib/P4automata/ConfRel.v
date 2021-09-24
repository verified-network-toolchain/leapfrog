Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
From Equations Require Import Equations.

Require Import Poulet4.Relations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.Ntuple.
Require Poulet4.P4automata.Syntax.
Module P4A := Poulet4.P4automata.Syntax.

Open Scope list_scope.

Lemma split_ex:
  forall A B (P: A * B -> Prop),
    (exists x: A, exists y: B, P (x, y)) <->
    exists x: A * B, P x.
Proof.
  firstorder.
  destruct x.
  firstorder.
Qed.

(* Bitstring variable context. *)
Inductive bctx :=
| BCEmp: bctx
| BCSnoc: bctx -> nat -> bctx.
Derive NoConfusion for bctx.
Derive EqDec for bctx.
Global Instance bctx_eq_dec : EquivDec.EqDec bctx eq := bctx_eqdec.

(* Bitstring variable valuation. *)
Fixpoint bval (c: bctx) : Type :=
  match c with
  | BCEmp => unit
  | BCSnoc c' size => bval c' * n_tuple bool size
  end.

Inductive bvar : bctx -> Type :=
| BVarTop:
    forall c size,
      bvar (BCSnoc c size)
| BVarRest:
    forall c size,
      bvar c ->
      bvar (BCSnoc c size).
Arguments BVarRest {_ _} _.
Derive NoConfusion for bvar.

Definition weaken_bvar {c} (size: nat) : bvar c -> bvar (BCSnoc c size) :=
  @BVarRest c size.

Equations bvar_eqdec {c} (x y: bvar c) : {x = y} + {x <> y} :=
  { bvar_eqdec (BVarTop _ _) (BVarTop _ _) := in_left;
    bvar_eqdec (BVarRest x') (BVarRest y') := if bvar_eqdec x' y'
                                              then in_left
                                              else in_right;
    bvar_eqdec _ _ := in_right }.
Next Obligation.
  dependent destruction H.
  eauto.
Qed.
#[global] Transparent bvar_eqdec.

Global Instance bvar_eq_dec {c}: EquivDec.EqDec (bvar c) eq := bvar_eqdec.

Fixpoint check_bvar {c} (x: bvar c) : nat :=
  match x with
  | BVarTop c size => size
  | BVarRest x' => check_bvar x'
  end.

Equations interp_bvar {c} (valu: bval c) (x: bvar c) : n_tuple bool (check_bvar x) :=
  { interp_bvar (_, bs)    (BVarTop _ _) := bs;
    interp_bvar (valu', bs) (BVarRest x') := interp_bvar valu' x' }.

Section ConfRel.
  Set Implicit Arguments.

  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Context `{H_finite: @Finite (P4A.H' H) _ (P4A.H'_eq_dec (H_eq_dec:=H_eq_dec))}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Record state_template :=
    { st_state: P4A.state_ref S;
      st_buf_len: nat }.

  Global Program Instance state_template_eq_dec : EquivDec.EqDec state_template eq :=
    { equiv_dec x y :=
        if x.(st_state) == y.(st_state)
        then if x.(st_buf_len) == y.(st_buf_len)
             then in_left
             else in_right
        else in_right }.
  Solve Obligations with (destruct x, y;
                           unfold equiv, complement in *;
                           simpl in *;
                           congruence).

  Definition interp_state_template (st: state_template) (c: conf) :=
    st.(st_state) = c.(conf_state) /\
    st.(st_buf_len) = c.(conf_buf_len).

  Lemma interp_state_template_dichotomy (t1 t2: state_template) (c: conf):
    interp_state_template t1 c ->
    interp_state_template t2 c ->
    t1 = t2.
  Proof.
    unfold interp_state_template; intros.
    destruct H0, H1.
    destruct t1, t2; simpl in *.
    congruence.
  Qed.

  Inductive side := Left | Right.
  Derive NoConfusion for side.
  Derive EqDec for side.

  Check (P4A.hdr_ref H).

  Inductive bit_expr (c: bctx) :=
  | BELit (l: list bool)
  | BEBuf (a: side)
  | BEHdr (a: side) (h: P4A.hdr_ref H)
  | BEVar (b: bvar c)
  | BESlice (e: bit_expr c) (hi lo: nat)
  | BEConcat (e1 e2: bit_expr c).
  Arguments BELit {c} _.
  Arguments BEBuf {c} _.
  Arguments BEHdr {c} _ _.
  Derive NoConfusion for bit_expr.

  Definition beslice {c} (be: bit_expr c) (hi lo: nat) :=
    match be with
    | BELit l => BELit (P4A.slice l hi lo)
    | BESlice x hi' lo' => BESlice x (Nat.min (lo' + hi) hi') (lo' + lo)
    | _ => BESlice be hi lo
    end.

  Definition beconcat {c} (l: bit_expr c) (r: bit_expr c) :=
    match l, r with
    | BELit l, BELit r => BELit (l ++ r)
    | _, _ => BEConcat l r
    end.

  Fixpoint weaken_bit_expr {c} (size: nat) (b: bit_expr c) : bit_expr (BCSnoc c size) :=
    match b with
    | BELit l => BELit l
    | BEBuf a => BEBuf a
    | BEHdr a h => BEHdr a h
    | BEVar b => BEVar (weaken_bvar size b)
    | BESlice e hi lo => BESlice (weaken_bit_expr size e) hi lo
    | BEConcat e1 e2 => BEConcat (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    end.

  Obligation Tactic := intros.
  Unset Transparent Obligations.
  Equations bit_expr_eq_dec {c: bctx} : forall x y: bit_expr c, {x = y} + {x <> y} :=
    { bit_expr_eq_dec (BELit l) (BELit l') :=
        if l == l' then in_left else in_right;
      bit_expr_eq_dec (BEBuf a) (BEBuf a') :=
        if side_eqdec a a' then in_left else in_right;
      bit_expr_eq_dec (BEHdr a h) (BEHdr a' h') :=
        if Sumbool.sumbool_and _ _ _ _ (side_eqdec a a') (h == h')
        then in_left
        else in_right;
      bit_expr_eq_dec (BEVar x) (BEVar x') :=
        if bvar_eq_dec x x'
        then in_left
        else in_right;
      bit_expr_eq_dec (BESlice e hi lo) (BESlice e' hi' lo') :=
        if Sumbool.sumbool_and _ _ _ _ (hi == hi') (lo == lo')
        then if bit_expr_eq_dec e e'
             then in_left
             else in_right
        else in_right;
      bit_expr_eq_dec (BEConcat e1 e2) (BEConcat e1' e2') :=
        if bit_expr_eq_dec e1 e1'
        then if bit_expr_eq_dec e2 e2'
             then in_left
             else in_right
        else in_right;
             bit_expr_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  #[global] Transparent bit_expr_eq_dec.

  Global Program Instance bit_expr_eqdec {c} : EquivDec.EqDec (bit_expr c) eq :=
    { equiv_dec := bit_expr_eq_dec }.

  Fixpoint be_size {c} b1 b2 (e: bit_expr c) : nat :=
    match e with
    | BELit l => List.length l
    | BEBuf side =>
      match side with
      | Left => b1
      | Right => b2
      end
    | BEHdr a (P4A.HRVar h) => projT1 h
    | BEVar x => check_bvar x
    | BESlice e hi lo =>
      Nat.min (1 + hi) (be_size b1 b2 e) - lo
    | BEConcat e1 e2 =>
      be_size b1 b2 e1 + be_size b1 b2 e2
    end.

  Equations interp_bit_expr {c} (e: bit_expr c) (valu: bval c) (c1 c2: conf)
    : n_tuple bool (be_size (conf_buf_len c1) (conf_buf_len c2) e) := {
    interp_bit_expr (BELit l) valu c1 c2 :=
      l2t l;
    interp_bit_expr (BEBuf Left) valu c1 c2 :=
      conf_buf c1;
    interp_bit_expr (BEBuf Right) valu c1 c2 :=
      conf_buf c2;
    interp_bit_expr (BEHdr a h) valu c1 c2 :=
      let c := match a with
               | Left => c1
               | Right => c2
               end
      in
      match h with
      | P4A.HRVar var =>
        match P4A.find H (projT2 var) (conf_store c)  with
        | P4A.VBits _ v => v
        end
      end;
    interp_bit_expr (BEVar x) valu c1 c2 :=
      interp_bvar valu x;
    interp_bit_expr (BESlice e hi lo) valu c1 c2 :=
      n_tuple_slice hi lo (interp_bit_expr e valu c1 c2);
    interp_bit_expr (BEConcat e1 e2) valu c1 c2 :=
      n_tuple_concat
        (interp_bit_expr e1 valu c1 c2)
        (interp_bit_expr e2 valu c1 c2)
  }.

  Inductive store_rel c :=
  | BRTrue
  | BRFalse
  | BREq (e1 e2: bit_expr c)
  | BRAnd (r1 r2: store_rel c)
  | BROr (r1 r2: store_rel c)
  | BRImpl (r1 r2: store_rel c).
  Arguments store_rel : default implicits.

  (* smart constructors *)

  Definition brand {c} (l: store_rel c) (r: store_rel c) :=
    (* BRAnd l r. *)
    match l with
    | BRTrue _ => r
    | BRFalse _ => BRFalse c
    | _ =>
      match r with
      | BRTrue _ => l
      | BRFalse _ => BRFalse c
      | _ => BRAnd l r
      end
    end.

  Definition bror {c} (l: store_rel c) (r: store_rel c) :=
    (* BROr l r. *)
    match l with
    | BRTrue _ => BRTrue c
    | BRFalse _ => r
    | _ =>
      match r with
      | BRTrue _ => BRTrue c
      | BRFalse _ => l
      | _ => BROr l r
      end
    end.

  Definition brimpl {c} (l: store_rel c) (r: store_rel c) :=
    (* BRImpl l r. *)
      match l with
      | BRTrue _ => r
      | BRFalse _ => BRTrue c
      | _ =>
        match r with
        | BRTrue _ => BRTrue c
        | _ => BRImpl l r
        end
      end.

  Equations store_rel_eq_dec {c: bctx} : forall x y: store_rel c, {x = y} + {x <> y} :=
    { store_rel_eq_dec (BRTrue _) (BRTrue _) := in_left;
      store_rel_eq_dec (BRFalse _) (BRFalse _) := in_left;
      store_rel_eq_dec (BREq e11 e12) (BREq e21 e22) :=
        if Sumbool.sumbool_and _ _ _ _ (e11 == e21) (e12 == e22)
        then in_left
        else in_right;
      store_rel_eq_dec (BRAnd r11 r12) (BRAnd r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BROr r11 r12) (BROr r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
      store_rel_eq_dec (BRImpl r11 r12) (BRImpl r21 r22) :=
        if (store_rel_eq_dec r11 r21)
        then if (store_rel_eq_dec r12 r22)
             then in_left
             else in_right
        else in_right;
    store_rel_eq_dec _ _ := in_right }.

  Solve All Obligations with
      (intros;
      repeat match goal with
             | H: _ /\ _|- _ => destruct H
             | H: _ \/ _ |- _ => destruct H
             | |- ?g => congruence
             end).
  #[global] Transparent store_rel_eq_dec.

  Global Program Instance store_rel_eqdec {c: bctx}: EquivDec.EqDec (store_rel c) eq :=
    store_rel_eq_dec.

  Fixpoint weaken_store_rel {c} (size: nat) (r: store_rel c) : store_rel (BCSnoc c size) :=
    match r with
    | BRTrue _ => BRTrue _
    | BRFalse _ => BRFalse _
    | BREq e1 e2 => BREq (weaken_bit_expr size e1) (weaken_bit_expr size e2)
    | BRAnd r1 r2 => brand (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BROr r1 r2 => bror (weaken_store_rel size r1) (weaken_store_rel size r2)
    | BRImpl r1 r2 => BRImpl (weaken_store_rel size r1) (weaken_store_rel size r2)
    end.

  Equations interp_store_rel {c} (r: store_rel c) (valu: bval c) (c1 c2: conf) : Prop := {
    interp_store_rel (BRTrue _) valu c1 c2 :=
      True;
    interp_store_rel (BRFalse _) valu c1 c2 :=
      False;
    interp_store_rel (BREq e1 e2) valu c1 c2 :=
      match eq_dec (be_size (conf_buf_len c1) (conf_buf_len c2) e1)
                   (be_size (conf_buf_len c1) (conf_buf_len c2) e2) with
      | left Heq =>
        eq_rect _ _ (interp_bit_expr e1 valu c1 c2) _ Heq =
        interp_bit_expr e2 valu c1 c2
      | right _ => False
      end;
    interp_store_rel (BRAnd r1 r2) valu c1 c2 :=
      interp_store_rel r1 valu c1 c2 /\ interp_store_rel r2 valu c1 c2;
    interp_store_rel (BROr r1 r2) valu c1 c2 :=
      interp_store_rel r1 valu c1 c2 \/ interp_store_rel r2 valu c1 c2;
    interp_store_rel (BRImpl r1 r2) valu c1 c2 :=
      interp_store_rel r1 valu c1 c2 -> interp_store_rel r2 valu c1 c2
  }.

  (* correctness of smart constructors *)
  Lemma bror_corr :
    forall c (l r: store_rel c) v c1 c2,
        interp_store_rel (BROr l r) v c1 c2 <-> interp_store_rel (bror l r) v c1 c2.
  Proof.
    split; intros; destruct l, r; unfold bror in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Lemma brand_corr :
    forall c (l r: store_rel c) v c1 c2,
        interp_store_rel (BRAnd l r) v c1 c2 <-> interp_store_rel (brand l r) v c1 c2.
  Proof.
    split; intros; destruct l, r; unfold brand in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Lemma brimpl_corr :
    forall c (l r: store_rel c) v c1 c2,
        interp_store_rel (BRImpl l r) v c1 c2 <-> interp_store_rel (brimpl l r) v c1 c2.
  Proof.
    split; intros; destruct l, r; unfold brimpl in *;
    autorewrite with interp_store_rel in *; auto; intuition.
  Qed.

  Record conf_states :=
    { cs_st1: state_template;
      cs_st2: state_template; }.
  Global Program Instance conf_states_eq_dec: EquivDec.EqDec conf_states eq :=
    { equiv_dec x y :=
        if x.(cs_st1) == y.(cs_st1)
        then if x.(cs_st2) == y.(cs_st2)
             then in_left
             else in_right
        else in_right }.
  Solve All Obligations with (destruct x, y; simpl in *; congruence).

  Record conf_rel :=
    { cr_st: conf_states;
      cr_ctx: bctx;
      cr_rel: store_rel cr_ctx }.
  Equations conf_rel_eq_dec: EquivDec.EqDec conf_rel eq :=
    { conf_rel_eq_dec x y with (bctx_eq_dec x.(cr_ctx) y.(cr_ctx)) :=
        { conf_rel_eq_dec ({| cr_st := st1;
                              cr_ctx := c;
                              cr_rel := rel1 |})
                          ({| cr_st := st2;
                              cr_ctx := c;
                              cr_rel := rel2 |})
                          (left eq_refl) :=
            if conf_states_eq_dec st1 st2
            then if store_rel_eq_dec rel1 rel2
                 then in_left
                 else in_right
            else in_right;
        conf_rel_eq_dec _ _ _ := in_right } }.
  Solve All Obligations with (try congruence).
  Next Obligation.
    intro Hs.
    inversion Hs.
    dependent destruction H2.
    eauto.
  Qed.
  #[global] Transparent conf_rel_eq_dec.

  Global Program Instance conf_rel_eqdec: EquivDec.EqDec conf_rel eq :=
    conf_rel_eq_dec.

  Definition interp_conf_state (c: conf_states) : relation conf :=
    fun c1 c2 =>
      interp_state_template c.(cs_st1) c1 /\
      interp_state_template c.(cs_st2) c2.

  Lemma interp_conf_state_dichotomy (s1 s2: conf_states) (c1 c2: conf):
    interp_conf_state s1 c1 c2 ->
    interp_conf_state s2 c1 c2 ->
    s1 = s2.
  Proof.
    unfold interp_conf_state; intros.
    destruct H0, H1.
    destruct s1, s2; simpl in *; f_equal.
    - now apply interp_state_template_dichotomy with (c := c1).
    - now apply interp_state_template_dichotomy with (c := c2).
  Qed.

  Definition interp_conf_rel (phi: conf_rel) : relation conf :=
    fun x y =>
      interp_conf_state phi.(cr_st) x y ->
      forall valu,
        interp_store_rel phi.(cr_rel) valu x y.

  Definition crel :=
    list (conf_rel).

  Notation "⊤" := rel_true.
  Notation "x ⊓ y" := (relation_conjunction x y) (at level 40).
  Notation "⟦ x ⟧" := (interp_conf_rel x).
  Definition interp_crel i (rel: crel) : relation conf :=
    interp_rels i (List.map interp_conf_rel rel).

  Lemma interp_crel_cons
    (i: relation conf)
    (c: conf_rel)
    (cs: crel)
    (c1 c2: conf)
  :
    interp_crel i (c :: cs) c1 c2 <->
    interp_conf_rel c c1 c2 /\ interp_crel i cs c1 c2.
  Proof.
    unfold interp_crel, interp_rels.
    now cbn.
  Qed.

  Record entailment :=
    { e_prem: crel;
      e_concl: conf_rel }.

  Definition interp_entailment (i: relation conf) (e: entailment) : relation conf :=
    fun q1 q2 =>
      interp_crel i e.(e_prem) q1 q2 ->
      interp_conf_rel e.(e_concl) q1 q2.

  Definition simplified_conf_rel := { ctx: bctx & store_rel ctx }.

  Definition interp_simplified_conf_rel
    (scr: simplified_conf_rel)
    (c1 c2: conf)
  :=
    forall valu, interp_store_rel (projT2 scr) valu c1 c2.

  Definition simplify_conf_rel (cr: conf_rel) :=
    existT _ cr.(cr_ctx) cr.(cr_rel).

  Lemma simplify_conf_rel_correct:
    forall cr c1 c2,
      interp_conf_rel cr c1 c2 <->
      (interp_conf_state cr.(cr_st) c1 c2 ->
       interp_simplified_conf_rel (simplify_conf_rel cr) c1 c2).
  Proof.
    unfold interp_simplified_conf_rel, interp_conf_rel.
    intuition.
  Qed.

  Definition simplified_crel := list simplified_conf_rel.

  Equations interp_simplified_crel
    (i: relation conf)
    (scrs: simplified_crel)
    (c1 c2: conf)
    : Prop
  := {
    interp_simplified_crel i nil c1 c2 => i c1 c2;
    interp_simplified_crel i (scr :: scrs) c1 c2 =>
    interp_simplified_conf_rel scr c1 c2 /\
    interp_simplified_crel i scrs c1 c2;
  }.

  Definition simplify_crel (crs: crel) (st: conf_states) :=
    let filtered := filter (equiv_decb st ∘ cr_st) crs in
    map simplify_conf_rel filtered.

  Lemma simplify_crel_correct (i: relation conf) (crs: crel) (st: conf_states):
    forall q1 q2,
      interp_conf_state st q1 q2 ->
      (interp_crel i crs q1 q2 <->
       interp_simplified_crel i (simplify_crel crs st) q1 q2).
  Proof.
    induction crs; intros.
    - unfold interp_crel; simpl.
      reflexivity.
    - rewrite interp_crel_cons.
      unfold simplify_crel.
      unfold compose; simpl.
      unfold equiv_decb at 1.
      destruct equiv_dec.
      + rewrite map_cons.
        autorewrite with interp_simplified_crel.
        rewrite filter_ext with (g := equiv_decb st ∘ cr_st) by auto.
        fold (simplify_crel crs st).
        rewrite IHcrs by auto.
        rewrite simplify_conf_rel_correct.
        rewrite <- e.
        intuition.
      + rewrite filter_ext with (g := equiv_decb st ∘ cr_st) by auto.
        fold (simplify_crel crs st).
        rewrite IHcrs by auto.
        intuition.
        unfold interp_conf_rel; intros.
        unfold Equivalence.equiv, complement in c.
        contradiction c.
        now apply interp_conf_state_dichotomy with (c1 := q1) (c2:= q2).
  Qed.

  Record simplified_entailment :=
    { se_st: conf_states;
      se_prems: simplified_crel;
      se_concl: simplified_conf_rel; }.

  Definition interp_simplified_entailment
    (i: relation conf)
    (se: simplified_entailment)
    : relation conf
  :=
    fun q1 q2 =>
      interp_conf_state se.(se_st) q1 q2 ->
      interp_simplified_crel i se.(se_prems) q1 q2 ->
      interp_simplified_conf_rel se.(se_concl) q1 q2.

  Definition simplify_entailment (e: entailment) :=
    let templates := e.(e_concl).(cr_st) in
    {|
      se_st := templates;
      se_prems := simplify_crel e.(e_prem) templates;
      se_concl := simplify_conf_rel e.(e_concl); |}.

  Lemma simplify_entailment_correct (e: entailment):
    forall i q1 q2,
      interp_entailment i e q1 q2 <->
      interp_simplified_entailment i (simplify_entailment e) q1 q2.
  Proof.
    intros.
    unfold interp_entailment, simplify_entailment, interp_simplified_entailment; simpl.
    split; intros.
    - apply simplify_conf_rel_correct; auto.
      apply H0.
      apply simplify_crel_correct with (st := e.(e_concl).(cr_st)); auto.
    - apply simplify_conf_rel_correct; intros.
      apply H0; auto.
      now apply simplify_crel_correct.
  Qed.
End ConfRel.
Arguments interp_conf_rel {_} {_} {_} {_} {_} _.
Arguments interp_crel {_} {_} {_} {_} {_} _.
Arguments interp_entailment {_} {_} {_} {_} {_} _.
