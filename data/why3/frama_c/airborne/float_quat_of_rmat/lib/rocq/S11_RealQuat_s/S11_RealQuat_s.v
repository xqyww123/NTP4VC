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
Open Scope Z_scope.
Inductive s11_realquat_s :=
  | s11_realquat_s'mk : R -> R -> R -> R -> s11_realquat_s.
Axiom s11_realquat_s_inhabited : Inhabited s11_realquat_s.
Global Existing Instance s11_realquat_s_inhabited.
Axiom s11_realquat_s_countable : Countable s11_realquat_s.
Global Existing Instance s11_realquat_s_countable.
Definition f11_realquat_s_qi (x : s11_realquat_s) := match x with |  s11_realquat_s'mk a _ _ _ => a end.
Definition f11_realquat_s_qx (x : s11_realquat_s) := match x with |  s11_realquat_s'mk _ a _ _ => a end.
Definition f11_realquat_s_qy (x : s11_realquat_s) := match x with |  s11_realquat_s'mk _ _ a _ => a end.
Definition f11_realquat_s_qz (x : s11_realquat_s) := match x with |  s11_realquat_s'mk _ _ _ a => a end.
Definition eqs11_realquat_s (s : s11_realquat_s) (s_1 : s11_realquat_s) := f11_realquat_s_qi s_1 = f11_realquat_s_qi s ∧ f11_realquat_s_qx s_1 = f11_realquat_s_qx s ∧ f11_realquat_s_qy s_1 = f11_realquat_s_qy s ∧ f11_realquat_s_qz s_1 = f11_realquat_s_qz s.
