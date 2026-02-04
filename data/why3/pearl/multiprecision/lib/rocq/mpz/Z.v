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
Open Scope Z_scope.
Axiom mpz_ptr : Type.
Axiom mpz_ptr_inhabited : Inhabited mpz_ptr.
Global Existing Instance mpz_ptr_inhabited.
Axiom mpz_ptr_countable : Countable mpz_ptr.
Global Existing Instance mpz_ptr_countable.
Axiom mpz_eq : mpz_ptr -> mpz_ptr -> Prop.
Axiom mpz_eq'spec : forall  (x : mpz_ptr) (y : mpz_ptr), mpz_eq x y = (x = y).
Axiom mpz_memo : Type.
Axiom mpz_memo_inhabited : Inhabited mpz_memo.
Global Existing Instance mpz_memo_inhabited.
Axiom mpz_memo_countable : Countable mpz_memo.
Global Existing Instance mpz_memo_countable.
Axiom abs_value_of : mpz_memo -> mpz_ptr -> Z.
Axiom alloc : mpz_memo -> mpz_ptr -> Z.
Axiom abs_size : mpz_memo -> mpz_ptr -> Z.
Axiom sgn : mpz_memo -> mpz_ptr -> Z.
Axiom readers : mpz_memo -> mpz_ptr -> Z.
Axiom zones : mpz_memo -> mpz_ptr -> zone.
Axiom mpz_memo'invariant : forall  (self : mpz_memo) (p : mpz_ptr), 0%Z ≤ alloc self p ∧ (sgn self p = 1%Z ∨ sgn self p = - 1%Z) ∧ abs_size self p ≤ alloc self p ∧ 0%Z ≤ abs_size self p ∧ abs_size self p ≤ 2147483647%Z ∧ 0%Z ≤ abs_value_of self p ∧ (1%Z ≤ abs_size self p -> Z.pow (18446744073709551615%Z + 1%Z) (abs_size self p - 1%Z) ≤ abs_value_of self p) ∧ abs_value_of self p < Z.pow (18446744073709551615%Z + 1%Z) (abs_size self p).
Definition value_of (x : mpz_ptr) (memo : mpz_memo) : Z := sgn memo x * abs_value_of memo x.
Definition sgn_value (p : ptr (bv 64%N)) (sz : bv 32%N) : Z := if decide (0%Z ≤ bv_signed sz) then value p (bv_signed sz) else - value p (- bv_signed sz).
Definition mpz_unchanged (x : mpz_ptr) (memo1 : mpz_memo) (memo2 : mpz_memo) := readers memo1 x = readers memo2 x ∧ (- 2%Z < readers memo1 x -> abs_value_of memo1 x = abs_value_of memo2 x ∧ alloc memo1 x = alloc memo2 x ∧ abs_size memo1 x = abs_size memo2 x ∧ sgn memo1 x = sgn memo2 x ∧ zones memo1 x = zones memo2 x).
Inductive mpz_struct :=
  | mpz_struct'mk : mpz_ptr -> mpz_struct.
Axiom mpz_struct_inhabited : Inhabited mpz_struct.
Global Existing Instance mpz_struct_inhabited.
Axiom mpz_struct_countable : Countable mpz_struct.
Global Existing Instance mpz_struct_countable.
Definition addr (x : mpz_struct) := match x with |  mpz_struct'mk a => a end.
