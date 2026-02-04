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
Require Import inner_product.A_InnerProductAxiomatic.A_InnerProductAxiomatic.
Require Import Why3.Cint.Cint.
Require Import inner_product.Compound.Compound.
Require Import inner_product.Axiomatic.Axiomatic.
Open Scope Z_scope.
Definition p_innerproductbounds (mint_0 : addr -> Z) (a : addr) (b : addr) (n : Z) (init_0 : Z) := ∀(i : Z), let x : Z := l_innerproduct mint_0 a b i init_0 in i ≤ n -> 0%Z ≤ i -> - 2147483648%Z ≤ x ∧ x ≤ 2147483647%Z.
Definition p_productbounds (mint_0 : addr -> Z) (a : addr) (b : addr) (n : Z) := ∀(i : Z), let x : Z := mint_0 (shift a i) * mint_0 (shift b i) in 0%Z ≤ i -> i < n -> - 2147483648%Z ≤ x ∧ x ≤ 2147483647%Z.
