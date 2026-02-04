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
Require Import Why3.why3.Ref.Ref.
Require Import multiprecision.types.Config.
Require Import Why3.mach.c.C.
Require Import Why3.mach.int.Unsigned.
Open Scope Z_scope.
Axiom limb : Type.
Axiom limb_inhabited : Inhabited limb.
Global Existing Instance limb_inhabited.
Axiom limb_countable : Countable limb.
Global Existing Instance limb_countable.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
