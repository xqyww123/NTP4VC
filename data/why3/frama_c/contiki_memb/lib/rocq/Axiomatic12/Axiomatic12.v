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
Require Import Why3.Memory.Memory.
Require Import contiki_memb.Compound.Compound.
Open Scope Z_scope.
Definition p_empty_block (malloc_0 : Z -> Z) (s : addr) := malloc_0 (base s) = 0%Z ∧ base_offset (offset s) = 0%Z.
Definition p_valid_or_empty (malloc_0 : Z -> Z) (s : addr) (n : Z) := valid_rw malloc_0 (shift s 0%Z) n ∧ (p_empty_block malloc_0 s ∨ valid_rd malloc_0 s 1%Z).
