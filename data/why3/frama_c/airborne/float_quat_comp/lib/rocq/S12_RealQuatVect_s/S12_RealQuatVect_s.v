From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.Qed.Qed.
Require Import float_quat_comp.S9_RealVect3_s.S9_RealVect3_s.
Open Scope Z_scope.
Inductive s12_realquatvect_s :=
  | s12_realquatvect_s'mk : R -> s9_realvect3_s -> s12_realquatvect_s.
Axiom s12_realquatvect_s_inhabited : Inhabited s12_realquatvect_s.
Global Existing Instance s12_realquatvect_s_inhabited.
Axiom s12_realquatvect_s_countable : Countable s12_realquatvect_s.
Global Existing Instance s12_realquatvect_s_countable.
Definition f12_realquatvect_s_scalar (x : s12_realquatvect_s) := match x with |  s12_realquatvect_s'mk a _ => a end.
Definition f12_realquatvect_s_vect (x : s12_realquatvect_s) := match x with |  s12_realquatvect_s'mk _ a => a end.
Definition eqs12_realquatvect_s (s : s12_realquatvect_s) (s_1 : s12_realquatvect_s) := f12_realquatvect_s_scalar s_1 = f12_realquatvect_s_scalar s ∧ eqs9_realvect3_s (f12_realquatvect_s_vect s) (f12_realquatvect_s_vect s_1).
