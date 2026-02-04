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
Require Import Why3.map.Const.
Require Import Why3.map.MapEq.
Require Import Why3.mach.c.C.
Require Import Why3.mach.int.Unsigned.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Open Scope Z_scope.
Axiom mem : Type.
Axiom mem_inhabited : Inhabited mem.
Global Existing Instance mem_inhabited.
Axiom mem_countable : Countable mem.
Global Existing Instance mem_countable.
Axiom zr : mem -> zone.
Axiom zx : mem -> zone.
Axiom zy : mem -> zone.
Axiom mr : mem -> bv 32%N.
Axiom mx : mem -> bv 32%N.
Axiom my : mem -> bv 32%N.
Axiom lr : mem -> bv 32%N.
Axiom lx : mem -> bv 32%N.
Axiom ly : mem -> bv 32%N.
Axiom ok : mem -> bool.
Definition identical (p1 : ptr (bv 64%N)) (p2 : ptr (bv 64%N)) := data p1 = data p2 ∧ offset p1 = offset p2 ∧ min p1 = min p2 ∧ C.max p1 = C.max p2 ∧ zone1 p1 = zone1 p2.
