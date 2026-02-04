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
Require Import multiprecision.lemmas.Lemmas.
Require Import Why3.mach.int.Unsigned.
Require Import Why3.mach.c.C.
Require Import Why3.mach.c.UChar.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Open Scope Z_scope.
Definition in_base (b : Z) (x : Z -> bv 8%N) (n : Z) (m : Z) := ∀(i : Z), n ≤ i ∧ i < m -> 0%Z ≤ bv_signed (x i) ∧ bv_signed (x i) < b.
Axiom svalue_le_sub : Z -> (Z -> bv 8%N) -> Z -> Z -> Z.
Axiom svalue_le_sub'def : forall  (n : Z) (m : Z) (b : Z) (x : Z -> bv 8%N), if decide (n < m) then svalue_le_sub b x n m = bv_signed (x n) + b * svalue_le_sub b x (n + 1%Z) m else svalue_le_sub b x n m = 0%Z.
Definition string_in_base (b : Z) (p : ptr (bv 8%N)) := in_base b (pelts p) (min p) (C.max p).
Definition svalue_le (b : Z) (x : ptr (bv 8%N)) (sz : Z) : Z := svalue_le_sub b (pelts x) (offset x) (offset x + sz).
Axiom svalue_sub : Z -> (Z -> bv 8%N) -> Z -> Z -> Z.
Axiom svalue_sub'def : forall  (n : Z) (m : Z) (b : Z) (x : Z -> bv 8%N), if decide (n < m) then svalue_sub b x n m = bv_signed (x (m - 1%Z)) + b * svalue_sub b x n (m - 1%Z) else svalue_sub b x n m = 0%Z.
Definition svalue (b : Z) (x : ptr (bv 8%N)) (sz : Z) : Z := svalue_sub b (pelts x) (offset x) (offset x + sz).
