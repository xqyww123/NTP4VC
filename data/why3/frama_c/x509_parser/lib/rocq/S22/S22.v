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
Inductive s22 :=
  | s22'mk : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> s22.
Axiom s22_inhabited : Inhabited s22.
Global Existing Instance s22_inhabited.
Axiom s22_countable : Countable s22.
Global Existing Instance s22_countable.
Definition f22_empty_subject (x : s22) := match x with |  s22'mk a _ _ _ _ _ _ _ _ _ _ _ _ _ _ => a end.
Definition f22_san_empty (x : s22) := match x with |  s22'mk _ a _ _ _ _ _ _ _ _ _ _ _ _ _ => a end.
Definition f22_san_critical (x : s22) := match x with |  s22'mk _ _ a _ _ _ _ _ _ _ _ _ _ _ _ => a end.
Definition f22_ca_true (x : s22) := match x with |  s22'mk _ _ _ a _ _ _ _ _ _ _ _ _ _ _ => a end.
Definition f22_bc_critical (x : s22) := match x with |  s22'mk _ _ _ _ a _ _ _ _ _ _ _ _ _ _ => a end.
Definition f22_has_ski (x : s22) := match x with |  s22'mk _ _ _ _ _ a _ _ _ _ _ _ _ _ _ => a end.
Definition f22_has_keyusage (x : s22) := match x with |  s22'mk _ _ _ _ _ _ a _ _ _ _ _ _ _ _ => a end.
Definition f22_keycertsign_set (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ a _ _ _ _ _ _ _ => a end.
Definition f22_crlsign_set (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ a _ _ _ _ _ _ => a end.
Definition f22_pathlenconstraint_set (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ a _ _ _ _ _ => a end.
Definition f22_has_name_constraints (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ _ a _ _ _ _ => a end.
Definition f22_has_crldp (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ _ _ a _ _ _ => a end.
Definition f22_one_crldp_has_all_reasons (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ _ _ _ a _ _ => a end.
Definition f22_aki_has_keyidentifier (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ _ _ _ _ a _ => a end.
Definition f22_self_signed (x : s22) := match x with |  s22'mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ a => a end.
