Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Poulet4.Relations.
Require Import Poulet4.P4automata.Ntuple.
From Equations Require Import Equations.

Record p4automaton := MkP4Automaton {
  store: Type;
  states: Type;
  size: states -> nat;
  update: forall (S: states), n_tuple bool (size S) -> store -> store;
  transitions: states -> store -> states + bool;
  cap: forall s, 0 < size s;
}.

Definition state_ref (a: p4automaton) : Type := states a + bool.

Equations size'
  (a: p4automaton)
  (s: state_ref a)
  : nat := {
  size' a (inl s) := size a s;
  size' a (inr _) := 1
}.

Equations update'
  (a: p4automaton)
  (s: state_ref a)
  (buf: n_tuple bool (size' a s))
  (st: store a)
  : store a := {
  update' a (inl s) buf st := update a s buf st;
  update' a (inr _) _ st := st
}.

Equations transitions'
  (a: p4automaton)
  (s: state_ref a)
  (st: store a)
  : state_ref a := {
  transitions' a (inl s) st := transitions a s st;
  transitions' a (inr b) st := inr b
}.

Lemma cap' (a: p4automaton): forall s, 0 < size' a s.
Proof.
  destruct s; auto.
  rewrite size'_equation_1.
  apply cap.
Qed.

Record configuration (a: p4automaton) := MkConfiguration {
  conf_state: state_ref a;
  conf_buf_len: nat;
  conf_buf: n_tuple bool conf_buf_len;
  conf_buf_sane: conf_buf_len < size' a conf_state;
  conf_store: store a
}.

Definition configuration_room_left {a: p4automaton} (c: configuration a) :=
  size' a (conf_state _ c) - conf_buf_len _ c.

Definition configuration_has_room {a: p4automaton} (c: configuration a) :=
  conf_buf_len _ c + 1 < size' a (conf_state _ c).

Definition initial_configuration
  {a: p4automaton}
  (state: states a)
  (store: store a)
:= {|
  conf_state := inl state;
  conf_buf_len := 0;
  conf_buf := tt : n_tuple bool 0;
  conf_buf_sane := cap a state;
  conf_store := store
|}.

Lemma squeeze {n m}: n < m -> m <= n+1 -> n+1 = m.
Proof.
  lia.
Qed.

Definition step
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
  : configuration a :=
  let buf_padded := n_tuple_app (conf_buf _ c) b in
  match le_lt_dec (size' a (conf_state _ c)) (conf_buf_len _ c + 1) with
  | left Hle =>
    let buf_full := eq_rect _ _ buf_padded _ (squeeze (conf_buf_sane _ c) Hle) in
    let conf_store' := update' a (conf_state _ c) buf_full (conf_store _ c) in
    let conf_state' := transitions' a (conf_state _ c) conf_store' in
    {|
      conf_state := conf_state';
      conf_buf := tt : n_tuple bool 0;
      conf_buf_sane := cap' _ conf_state';
      conf_store := conf_store';
    |}
  | right conf_buf_sane' =>
    {|
      conf_state := conf_state _ c;
      conf_buf := buf_padded;
      conf_buf_sane := conf_buf_sane';
      conf_store := conf_store _ c;
    |}
  end.

Equations follow
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : configuration a := {
  follow c nil := c;
  follow c (b :: input) := follow (step c b) input
}.

Lemma follow_append
  {a: p4automaton}
  (c: configuration a)
  (buf: list bool)
  (b: bool):
  follow c (buf ++ [b]) = step (follow c buf) b.
Proof.
  revert c; induction buf; intros.
  - now autorewrite with follow.
  - rewrite <- app_comm_cons.
    autorewrite with follow.
    now rewrite IHbuf.
Qed.

Definition accepting
  {a: p4automaton}
  (c: configuration a)
  : Prop
:=
  conf_state _ c = inr true
.

Definition accepted
  {a: p4automaton}
  (c: configuration a)
  (input: list bool)
  : Prop
:=
  accepting (follow c input)
.

Definition lang_equiv
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
:=
  forall input,
    accepted c1 input <->
    accepted c2 input
.

Definition rel a1 a2 := configuration a1 -> configuration a2 -> Prop.
