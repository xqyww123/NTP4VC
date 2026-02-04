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
Require Import multiprecision.stringlemmas.String_lemmas.
Require Import multiprecision.lemmas.Lemmas.
Require Import Why3.mach.int.Unsigned.
Require Import Why3.mach.c.C.
Require Import Why3.mach.c.String.
Require Import Why3.mach.c.UChar.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.stringlemmas.Conversions.
Open Scope Z_scope.
Axiom abs_value_sub_text : Z -> (Z -> ascii) -> Z -> Z -> Z.
Axiom abs_value_sub_text'def : forall  (n : Z) (m : Z) (b : Z) (s : Z -> ascii), if decide (n < m) then abs_value_sub_text b s n m = text_to_num b (s (m - 1%Z)) + b * abs_value_sub_text b s n (m - 1%Z) else abs_value_sub_text b s n m = 0%Z.
Definition abs_value_text (b : Z) (s : Z -> ascii) (ofs : Z) : Z := abs_value_sub_text b s ofs (ofs + strlen s ofs).
Definition value_text (b : Z) (s : Z -> ascii) (ofs : Z) : Z := if decide (s ofs = get_str_i "-"%string 0%Z) then - abs_value_text b s (ofs + 1%Z) else abs_value_text b s ofs.
Definition text_in_base (b : Z) (t : Z -> ascii) (n : Z) (m : Z) := ∀(i : Z), n ≤ i ∧ i < m -> 0%Z ≤ text_to_num b (t i) ∧ text_to_num b (t i) < b.
Definition string_in_base (b : Z) (s : Z -> ascii) (ofs : Z) := text_in_base b s ofs (ofs + strlen s ofs) ∧ 0%Z < strlen s ofs ∨ s ofs = get_str_i "-"%string 0%Z ∧ text_in_base b s (ofs + 1%Z) (ofs + strlen s ofs) ∧ 1%Z < strlen s ofs.
