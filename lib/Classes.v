
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Require Import Coq.Classes.EquivDec.
From Equations Require Import Equations.

Global Instance N_eq_dec : EquivDec.EqDec N eq := N.eq_dec.
Global Instance N_eqdec : Classes.EqDec N := N_eq_dec.