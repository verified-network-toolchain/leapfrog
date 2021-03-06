Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Timestamp.

Notation H := (TimestampRefZeroSingle.header + TimestampSpecSingle.header).
Notation A := (Sum.sum TimestampRefZeroSingle.aut TimestampSpecSingle.aut).
Notation conf := (P4automaton.configuration (P4A.interp A)).
Notation start_left := TimestampRefZeroSingle.Start.
Notation start_right := TimestampSpecSingle.Start.

Definition r_states : {r : Reachability.state_pairs A & Reachability.reachable_states_wit start_left start_right r}.
  econstructor.
  unfold Reachability.reachable_states_wit.
  solve_fp_wit.
Defined.

(* Definition r_len := Eval vm_compute in (length r_states).

Print r_len. *)

Declare ML Module "mirrorsolve".

(*
RegisterEnvCtors
  (TimestampRefZeroSingle.Typ, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefZeroSingle.Len, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefZeroSingle.Value, FirstOrderConfRelSimplified.Bits 48)
  (TimestampRefZeroSingle.Scratch8, FirstOrderConfRelSimplified.Bits 8)
  (TimestampRefZeroSingle.Scratch16, FirstOrderConfRelSimplified.Bits 16)
  (TimestampRefZeroSingle.Scratch24, FirstOrderConfRelSimplified.Bits 24)
  (TimestampRefZeroSingle.Scratch32, FirstOrderConfRelSimplified.Bits 32)
  (TimestampRefZeroSingle.Scratch40, FirstOrderConfRelSimplified.Bits 40)
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
                   (projT1 r_states)
                   (wp (a := A))
                   []
                   (mk_init _ _ _ _ A start_left start_right)
                   q1 q2.
Proof.
  idtac "running timestamp single bisimulation".

  intros.
  set (a := A).
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
    try rewrite H16;
    try match goal with
    | |- pre_bisimulation _ _ _ (?N :: ?N' :: ?T) _ _ _  =>
      let rs := fresh "rs" in
      set (rs := N' :: T);
      let r := fresh "r" in
      set (r := N)

    | |- pre_bisimulation _ _ _ (?N :: nil) _ _ _  =>
      let r := fresh "r" in
      set (r := N)
    end
  ).
  time "close phase" close_bisim top'.

Time Admitted.
