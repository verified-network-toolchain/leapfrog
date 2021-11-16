Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.IPOptions.
Require Import Poulet4.P4automata.Benchmarks.Timestamp.

Notation H := (IPOptionsRef63.header + TimestampSpec3.header).
Notation A := (Sum.sum IPOptionsRef63.aut TimestampSpec3.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := IPOptionsRef63.Parse0.
Notation start_right := TimestampSpec3.Parse0.

Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        A
                        9
                        start_left
                        start_right).

(* Definition r_states' :=
  Eval vm_compute in (Reachability.reachable_step r_states).

Definition r_len := Eval vm_compute in (length r_states, length r_states').

Print r_len. *)

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (IPOptionsRef63.T0, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.L0, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.V0, FirstOrderConfRelSimplified.Bits 48)
  (IPOptionsRef63.T1, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.L1, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.V1, FirstOrderConfRelSimplified.Bits 48)
  (IPOptionsRef63.T2, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.L2, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.V2, FirstOrderConfRelSimplified.Bits 48)
  (IPOptionsRef63.Scratch8, FirstOrderConfRelSimplified.Bits 8)
  (IPOptionsRef63.Scratch16, FirstOrderConfRelSimplified.Bits 16)
  (IPOptionsRef63.Scratch24, FirstOrderConfRelSimplified.Bits 24)
  (IPOptionsRef63.Scratch32, FirstOrderConfRelSimplified.Bits 32)
  (IPOptionsRef63.Scratch40, FirstOrderConfRelSimplified.Bits 40)

  (TimestampSpec3.T0, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.L0, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.V0, FirstOrderConfRelSimplified.Bits 48)
  (TimestampSpec3.T1, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.L1, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.V1, FirstOrderConfRelSimplified.Bits 48)
  (TimestampSpec3.T2, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.L2, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.V2, FirstOrderConfRelSimplified.Bits 48)
  (TimestampSpec3.Scratch8, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.Scratch16, FirstOrderConfRelSimplified.Bits 16)
  (TimestampSpec3.Scratch24, FirstOrderConfRelSimplified.Bits 24)
  (TimestampSpec3.Scratch32, FirstOrderConfRelSimplified.Bits 32)
  (TimestampSpec3.Scratch40, FirstOrderConfRelSimplified.Bits 40)
  (TimestampSpec3.Pointer, FirstOrderConfRelSimplified.Bits 8)
  (TimestampSpec3.Overflow, FirstOrderConfRelSimplified.Bits 4)
  (TimestampSpec3.Flag, FirstOrderConfRelSimplified.Bits 4)
  (TimestampSpec3.Timestamp, FirstOrderConfRelSimplified.Bits 32).
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
                   (mk_init _ _ _ A 9 start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp three bisimulation".

  intros.
  set (a := A).
  set (rel0 := (mk_init _ _ _ _ _ _ _)).
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
  time "close phase" close_bisim top'.

Time Admitted.
