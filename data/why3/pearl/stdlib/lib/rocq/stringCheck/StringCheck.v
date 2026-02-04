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
Require Import Why3.string.StringRealization.
Open Scope Z_scope.
Axiom concat_assoc : forall  (s1 : string) (s2 : string) (s3 : string), concat (concat s1 s2) s3 = concat s1 (concat s2 s3).
Axiom concat_empty : forall  (s : string), concat s ""%string = concat ""%string s ∧ concat ""%string s = s.
Axiom length_empty : StringRealization.length ""%string = 0%Z.
Axiom length_concat : forall  (s1 : string) (s2 : string), StringRealization.length (concat s1 s2) = StringRealization.length s1 + StringRealization.length s2.
Axiom lt_empty : forall  (s : string) (fact0 : ¬ s = ""%string), lt ""%string s.
Axiom lt_not_com : forall  (s1 : string) (s2 : string) (fact0 : lt s1 s2), ¬ lt s2 s1.
Axiom lt_ref : forall  (s1 : string), ¬ lt s1 s1.
Axiom lt_trans : forall  (s1 : string) (s2 : string) (s3 : string) (fact0 : lt s1 s2) (fact1 : lt s2 s3), lt s1 s3.
Axiom le_empty : forall  (s : string), le ""%string s.
Axiom le_ref : forall  (s1 : string), le s1 s1.
Axiom lt_le : forall  (s1 : string) (s2 : string) (fact0 : lt s1 s2), le s1 s2.
Axiom lt_le_eq : forall  (s1 : string) (s2 : string) (fact0 : le s1 s2), lt s1 s2 ∨ s1 = s2.
Axiom le_trans : forall  (s1 : string) (s2 : string) (s3 : string) (fact0 : le s1 s2) (fact1 : le s2 s3), le s1 s3.
Axiom at_out_of_range : forall  (i : Z) (s : string) (fact0 : i < 0%Z ∨ StringRealization.length s ≤ i), s_at s i = ""%string.
Axiom at_empty : forall  (i : Z), s_at ""%string i = ""%string.
Axiom at_length : forall  (s : string) (i : Z), if decide (0%Z ≤ i ∧ i < StringRealization.length s) then StringRealization.length (s_at s i) = 1%Z else StringRealization.length (s_at s i) = 0%Z.
Axiom concat_at : forall  (s1 : string) (s2 : string), ∀(i : Z), (0%Z ≤ i ∧ i < StringRealization.length s1 -> s_at (concat s1 s2) i = s_at s1 i) ∧ (StringRealization.length s1 ≤ i ∧ i < StringRealization.length (concat s1 s2) -> s_at (concat s1 s2) i = s_at s2 (i - StringRealization.length s1)).
Axiom substring_out_of_range : forall  (i : Z) (s : string) (x : Z) (fact0 : i < 0%Z ∨ StringRealization.length s ≤ i), StringRealization.substring s i x = ""%string.
Axiom substring_of_length_zero_or_less : forall  (x : Z) (s : string) (i : Z) (fact0 : x ≤ 0%Z), StringRealization.substring s i x = ""%string.
Axiom substring_of_empty : forall  (i : Z) (x : Z), StringRealization.substring ""%string i x = ""%string.
Axiom substring_smaller : forall  (s : string) (i : Z) (x : Z), StringRealization.length (StringRealization.substring s i x) ≤ StringRealization.length s.
Axiom substring_smaller_x : forall  (x : Z) (s : string) (i : Z) (fact0 : 0%Z ≤ x), StringRealization.length (StringRealization.substring s i x) ≤ x.
Axiom substring_length : forall  (x : Z) (i : Z) (s : string) (fact0 : 0%Z ≤ x) (fact1 : 0%Z ≤ i) (fact2 : i < StringRealization.length s), if decide (StringRealization.length s < i + x) then StringRealization.length (StringRealization.substring s i x) = StringRealization.length s - i else StringRealization.length (StringRealization.substring s i x) = x.
Axiom substring_at : forall  (s : string) (i : Z), s_at s i = StringRealization.substring s i 1%Z.
Axiom substring_substring : forall  (ofs : Z) (s : string) (len : Z) (ofs' : Z) (len' : Z) (fact0 : 0%Z ≤ ofs) (fact1 : ofs ≤ StringRealization.length s) (fact2 : 0%Z ≤ len) (fact3 : ofs + len ≤ StringRealization.length s) (fact4 : 0%Z ≤ ofs') (fact5 : ofs' ≤ len) (fact6 : 0%Z ≤ len') (fact7 : ofs' + len' ≤ len), StringRealization.substring (StringRealization.substring s ofs len) ofs' len' = StringRealization.substring s (ofs + ofs') len'.
Axiom concat_substring : forall  (ofs : Z) (s : string) (len : Z) (len' : Z) (fact0 : 0%Z ≤ ofs) (fact1 : ofs ≤ StringRealization.length s) (fact2 : 0%Z ≤ len) (fact3 : ofs + len ≤ StringRealization.length s) (fact4 : 0%Z ≤ len') (fact5 : 0%Z ≤ ofs + len + len') (fact6 : ofs + len + len' ≤ StringRealization.length s), concat (StringRealization.substring s ofs len) (StringRealization.substring s (ofs + len) len') = StringRealization.substring s ofs (len + len').
Axiom prefixof_substring : forall  (s1 : string) (s2 : string), prefixof s1 s2 = (s1 = StringRealization.substring s2 0%Z (StringRealization.length s1)).
Axiom prefixof_concat : forall  (s1 : string) (s2 : string), prefixof s1 (concat s1 s2).
Axiom prefixof_empty : forall  (s2 : string), prefixof ""%string s2.
Axiom prefixof_empty2 : forall  (s1 : string) (fact0 : ¬ s1 = ""%string), ¬ prefixof s1 ""%string.
Axiom suffixof_substring : forall  (s1 : string) (s2 : string), suffixof s1 s2 = (s1 = StringRealization.substring s2 (StringRealization.length s2 - StringRealization.length s1) (StringRealization.length s1)).
Axiom suffixof_concat : forall  (s2 : string) (s1 : string), suffixof s2 (concat s1 s2).
Axiom suffixof_empty : forall  (s2 : string), suffixof ""%string s2.
Axiom suffixof_empty2 : forall  (s1 : string) (fact0 : ¬ s1 = ""%string), ¬ suffixof s1 ""%string.
Axiom contains_prefixof : forall  (s1 : string) (s2 : string) (fact0 : prefixof s1 s2), contains s2 s1.
Axiom contains_suffixof : forall  (s1 : string) (s2 : string) (fact0 : suffixof s1 s2), contains s2 s1.
Axiom contains_empty : forall  (s2 : string), contains ""%string s2 = (s2 = ""%string).
Axiom contains_empty2 : forall  (s1 : string), contains s1 ""%string.
Axiom contains_substring : forall  (s1 : string) (i : Z) (s2 : string) (fact0 : StringRealization.substring s1 i (StringRealization.length s2) = s2), contains s1 s2.
Axiom contains_concat : forall  (s1 : string) (s2 : string), contains (concat s1 s2) s1 ∧ contains (concat s1 s2) s2.
Axiom contains_at : forall  (s1 : string) (i : Z) (s2 : string) (fact0 : s_at s1 i = s2), contains s1 s2.
Axiom indexof_empty : forall  (i : Z) (s : string) (fact0 : 0%Z ≤ i) (fact1 : i ≤ StringRealization.length s), indexof s ""%string i = i.
Axiom indexof_empty1 : forall  (s : string) (i : Z), indexof ""%string s i = - 1%Z ∨ s = ""%string ∧ i = indexof ""%string s i ∧ indexof ""%string s i = 0%Z.
Axiom indexof_contains : forall  (s1 : string) (s2 : string), contains s1 s2 -> (0%Z ≤ indexof s1 s2 0%Z ∧ indexof s1 s2 0%Z ≤ StringRealization.length s1) ∧ StringRealization.substring s1 (indexof s1 s2 0%Z) (StringRealization.length s2) = s2.
Axiom contains_indexof : forall  (s1 : string) (s2 : string) (i : Z) (fact0 : 0%Z ≤ indexof s1 s2 i), contains s1 s2.
Axiom not_contains_indexof : forall  (s1 : string) (s2 : string) (i : Z) (fact0 : ¬ contains s1 s2), indexof s1 s2 i = - 1%Z.
Axiom substring_indexof : forall  (s1 : string) (s2 : string) (i : Z), 0%Z ≤ indexof s1 s2 i -> StringRealization.substring s1 (indexof s1 s2 i) (StringRealization.length s2) = s2.
Axiom indexof_out_of_range : forall  (i : Z) (s1 : string) (s2 : string) (fact0 : ¬ (0%Z ≤ i ∧ i ≤ StringRealization.length s1)), indexof s1 s2 i = - 1%Z.
Axiom indexof_in_range : forall  (s1 : string) (s2 : string) (i : Z), 0%Z ≤ i ∧ i ≤ StringRealization.length s1 -> indexof s1 s2 i = - 1%Z ∨ i ≤ indexof s1 s2 i ∧ indexof s1 s2 i ≤ StringRealization.length s1.
Axiom indexof_contains_substring : forall  (i : Z) (s1 : string) (s2 : string) (fact0 : 0%Z ≤ i) (fact1 : i ≤ StringRealization.length s1) (fact2 : contains (StringRealization.substring s1 i (StringRealization.length s1 - i)) s2), i ≤ indexof s1 s2 i ∧ indexof s1 s2 i ≤ StringRealization.length s1.
Axiom replace_empty : forall  (s1 : string) (s3 : string), replace s1 ""%string s3 = concat s3 s1.
Axiom replace_not_contains : forall  (s1 : string) (s2 : string) (s3 : string) (fact0 : ¬ contains s1 s2), replace s1 s2 s3 = s1.
Axiom replace_empty2 : forall  (s2 : string) (s3 : string), if decide (s2 = ""%string) then replace ""%string s2 s3 = s3 else replace ""%string s2 s3 = ""%string.
Axiom replace_substring_indexof : forall  (s1 : string) (s2 : string) (s3 : string), replace s1 s2 s3 = (if decide (indexof s1 s2 0%Z < 0%Z) then s1 else concat (concat (StringRealization.substring s1 0%Z (indexof s1 s2 0%Z)) s3) (StringRealization.substring s1 (indexof s1 s2 0%Z + StringRealization.length s2) (StringRealization.length s1 - indexof s1 s2 0%Z - StringRealization.length s2))).
Axiom replaceall_empty1 : forall  (s1 : string) (s3 : string), replaceall s1 ""%string s3 = s1.
Axiom not_contains_replaceall : forall  (s1 : string) (s2 : string) (s3 : string) (fact0 : ¬ contains s1 s2), replaceall s1 s2 s3 = s1.
Axiom to_int_gt_minus_1 : forall  (s : string), - 1%Z ≤ to_int s.
Axiom to_int_empty : to_int ""%string = - 1%Z.
Definition is_digit (s : string) := (0%Z ≤ to_int s ∧ to_int s ≤ 9%Z) ∧ StringRealization.length s = 1%Z.
Axiom from_int_negative : forall  (i : Z), (i < 0%Z) = (from_int i = ""%string).
Axiom from_int_to_int : forall  (i : Z), if decide (0%Z ≤ i) then to_int (from_int i) = i else to_int (from_int i) = - 1%Z.
