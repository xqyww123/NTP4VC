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
Require Import Why3.mach.int.Unsigned.
Require Import Why3.mach.c.C.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.compare.Compare.
Require Import multiprecision.util.Util.
Require Import multiprecision.ptralias.Alias.
Require Import multiprecision.util.UtilOld.
Require Import multiprecision.add.Add.
Require Import multiprecision.add.AddOld.
Require Import multiprecision.sub.SubOld.
Require Import multiprecision.logical.LogicalUtil.
Require Import multiprecision.logical.LogicalOld.
Require Import multiprecision.mul.Mul.
Open Scope Z_scope.
Definition reciprocal (v : bv 64%N) (d : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned d) - (18446744073709551615%Z + 1%Z).
Definition reciprocal_3by2 (v : bv 64%N) (dh : bv 64%N) (dl : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh) - (18446744073709551615%Z + 1%Z).
Definition normalized (x : ptr (bv 64%N)) (sz : bv 32%N) := valid x (bv_signed sz) ∧ ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned (pelts x (offset x + bv_signed sz - 1%Z)).
