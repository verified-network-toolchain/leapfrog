Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Notation H := (TimestampRefKeepSingle.header + TimestampSpecSingle.header).
Notation A := (Sum.sum TimestampRefKeepSingle.aut TimestampSpecSingle.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := TimestampRefKeepSingle.Start.
Notation start_right := TimestampSpecSingle.Start.

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        2
                        start_left
                        start_right).

(* Definition r_len := Eval vm_compute in (length r_states).

Print r_len. *)

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (TimestampRefKeepSingle.Typ, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefKeepSingle.Len, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefKeepSingle.Value, FirstOrderConfRelSimplified.Bits 48)
  (TimestampRefKeepSingle.Scratch8, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefKeepSingle.Scratch16, FirstOrderConfRelSimplified.Bits 16)
  (TimestampRefKeepSingle.Scratch24, FirstOrderConfRelSimplified.Bits 24)
  (TimestampRefKeepSingle.Scratch32, FirstOrderConfRelSimplified.Bits 32)
  (TimestampRefKeepSingle.Scratch40, FirstOrderConfRelSimplified.Bits 40)
  (TimestampSpecSingle.Typ, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSingle.Len, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSingle.Scratch8, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSingle.Scratch16, FirstOrderConfRelSimplified.Bits 16)
  (TimestampSpecSingle.Scratch24, FirstOrderConfRelSimplified.Bits 24)
  (TimestampSpecSingle.Scratch32, FirstOrderConfRelSimplified.Bits 32)
  (TimestampSpecSingle.Scratch40, FirstOrderConfRelSimplified.Bits 40)
  (TimestampSpecSingle.Scratch48, FirstOrderConfRelSimplified.Bits 48)
  (TimestampSpecSingle.Pointer, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpecSingle.Overflow, FirstOrderConfRelSimplified.Bits 4)
  (TimestampSpecSingle.Flag, FirstOrderConfRelSimplified.Bits 4)
  (TimestampSpecSingle.Timestamp, FirstOrderConfRelSimplified.Bits 32).
*)

  Lemma prebisim_incremental_sep:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (start_left));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (start_right));
                          st_buf_len := 0;
                        |};
                      |};
                      cr_ctx := BCEmp;
                      cr_rel := btrue;
                   |} q1 q2 ->
  pre_bisimulation A
                   (wp r_states)
                   top
                   []
                   (mk_init _ _ _ _ A 2 start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp single bisimulation".

  intros.
  set (a := A).
  (* vm_compute in a. *)
  (* Set Ltac Profiling. *)

  set (rel0 := (mk_init _ _ _ _ _ _ _ _)).
  vm_compute in rel0.
  subst rel0.

  set (eight := 8).
  assert (H8 : 8 = eight); [subst eight; reflexivity|].
  set (sixteen := (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight))))))))).
  assert (H16 : (Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S( Datatypes.S eight)))))))) = sixteen); [subst sixteen; reflexivity|].


  try rewrite H8;
  try rewrite H16;


  match goal with
  | |- pre_bisimulation _ _ _ _ ?R _ _ =>
    hashcons_list R
  end.

  time "build phase" repeat (run_bisim top top' r_states;
    try rewrite H8;
    try rewrite H16
  ).

  (* Show Ltac Profile. *)
  time "close phase" close_bisim top'.

Time Admitted.
