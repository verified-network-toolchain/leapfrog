Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.SloppyStrict.

Notation H := (Sloppy.header + Strict.header).
Notation A := SloppyStrict.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        SloppyStrict.aut
                        200
                        Sloppy.ParseEthernet
                        Strict.ParseEthernet).

Definition top : Relations.rel conf := fun _ _ => True.
Definition top' : Relations.rel (state_template A) := fun _ _ => True.

Declare ML Module "mirrorsolve".

RegisterEnvCtors
  (Sloppy.HdrEthernet, FirstOrderConfRelSimplified.Bits 112)
  (Sloppy.HdrIPv4, FirstOrderConfRelSimplified.Bits 128)
  (Sloppy.HdrIPv6, FirstOrderConfRelSimplified.Bits 288)
  (Strict.HdrEthernet, FirstOrderConfRelSimplified.Bits 112)
  (Strict.HdrIPv4, FirstOrderConfRelSimplified.Bits 128)
  (Strict.HdrIPv6, FirstOrderConfRelSimplified.Bits 288).

  Definition not_equally_accepting (s: Reachability.state_pair A) : bool :=
    let '(s1, s2) := s in
    match s1.(st_state), s2.(st_state) with
    | inr true, inr true => false
    | inr true, _ => true
    | _, inr true => true
    | _, _ => false
    end.

  Definition mk_rel '((s1, s2): Reachability.state_pair A)
    : conf_rel A :=
    {| cr_st := {| cs_st1 := s1;
                   cs_st2 := s2 |};
       cr_ctx := BCEmp;
       cr_rel := BRImpl
                     (BROr (BREq (BESlice (BEHdr _ Left (P4A.HRVar (existT _ _ (inl Sloppy.HdrEthernet)))) 111 96)
                                   (BELit _ _ [true; false; false; false;
                                           false; true; true; false;
                                           false; false; false; false;
                                           false; false; false; false]))
                           (BREq (BESlice (BEHdr _ Left (P4A.HRVar (existT _ _ (inl Sloppy.HdrEthernet)))) 111 96)
                                   (BELit _ _ [true; false; false; false;
                                           false; true; true; false;
                                           true; true; false; true;
                                           true; true; false; true])))
                     bfalse
       |}.

  Definition mk_partition (r: Reachability.state_pairs A) : crel A :=
    List.map mk_rel (List.filter not_equally_accepting r).

  Definition mk_init' (n: nat) s1 s2 :=
    List.nodup (@conf_rel_eq_dec _ _ _ _ _ _ A)
               (mk_partition (Reachability.reachable_states A n s1 s2)).

Lemma prebisim_sloppystrict:
  forall q1 q2,
    interp_conf_rel' {| cr_st := {|
                        cs_st1 := {|
                          st_state := inl (inl (Sloppy.ParseEthernet));
                          st_buf_len := 0;
                        |};
                        cs_st2 := {|
                          st_state := inl (inr (Strict.ParseEthernet));
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
                   (mk_init' 200 Sloppy.ParseEthernet Strict.ParseEthernet)
                   q1 q2.
Proof.
  idtac "running sloppystrict bisimulation".

  intros.
  set (rel0 := (mk_init' 200 Sloppy.ParseEthernet Strict.ParseEthernet)).
  vm_compute in rel0.
  subst rel0.

  time "build phase" repeat (time "single step" run_bisim top top' r_states).
  time "close phase" close_bisim top'.
Time Admitted.
