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
Require Import Why3.mach.c.String.
Require Import Why3.mach.c.UChar.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Open Scope Z_scope.
Definition num_to_lowercase_text (d : bv 8%N) : ascii := if decide (0%Z ≤ bv_signed d ∧ bv_signed d < 36%Z) then get_str_i "0123456789abcdefghijklmnopqrstuvwxyz"%string (bv_signed d) else Ascii.ascii_of_nat (Z.to_nat (- 1%Z)).
Definition to_lowercase_text (d : Z -> bv 8%N) (t : Z -> ascii) (m : Z) (n : Z) := ∀(i : Z), n ≤ i ∧ i < m -> t i = num_to_lowercase_text (d i).
Definition num_to_uppercase_text (d : bv 8%N) : ascii := if decide (0%Z ≤ bv_signed d ∧ bv_signed d < 36%Z) then get_str_i "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"%string (bv_signed d) else Ascii.ascii_of_nat (Z.to_nat (- 1%Z)).
Definition to_uppercase_text (d : Z -> bv 8%N) (t : Z -> ascii) (m : Z) (n : Z) := ∀(i : Z), n ≤ i ∧ i < m -> t i = num_to_uppercase_text (d i).
Definition num_to_bothcase_text (d : bv 8%N) : ascii := if decide (0%Z ≤ bv_signed d ∧ bv_signed d < 62%Z) then get_str_i "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"%string (bv_signed d) else Ascii.ascii_of_nat (Z.to_nat (- 1%Z)).
Definition to_bothcase_text (d : Z -> bv 8%N) (t : Z -> ascii) (m : Z) (n : Z) := ∀(i : Z), n ≤ i ∧ i < m -> t i = num_to_bothcase_text (d i).
Definition text_to_num_onecase (c : ascii) : Z := if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "0"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "9"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "0"%string 0%Z)) else if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "a"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "z"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "a"%string 0%Z)) + 10%Z else if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "A"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "Z"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "A"%string 0%Z)) + 10%Z else - 1%Z.
Definition text_to_num_bothcase (c : ascii) : Z := if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "0"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "9"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "0"%string 0%Z)) else if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "a"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "z"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "a"%string 0%Z)) + 36%Z else if decide (Z.of_nat (Ascii.nat_of_ascii (get_str_i "A"%string 0%Z)) ≤ Z.of_nat (Ascii.nat_of_ascii c) ∧ Z.of_nat (Ascii.nat_of_ascii c) ≤ Z.of_nat (Ascii.nat_of_ascii (get_str_i "Z"%string 0%Z))) then Z.of_nat (Ascii.nat_of_ascii c) - Z.of_nat (Ascii.nat_of_ascii (get_str_i "A"%string 0%Z)) + 10%Z else - 1%Z.
Definition text_to_num (base : Z) (c : ascii) : Z := if decide (- 36%Z ≤ base ∧ base ≤ 36%Z) then text_to_num_onecase c else text_to_num_bothcase c.
Definition num_to_text (base : Z) (d : bv 8%N) : ascii := if decide (0%Z ≤ base ∧ base ≤ 36%Z) then num_to_lowercase_text d else if decide (36%Z < base ∧ base ≤ 62%Z) then num_to_bothcase_text d else if decide (- 36%Z ≤ base) then num_to_uppercase_text d else Ascii.ascii_of_nat (Z.to_nat (- 1%Z)).
Definition to_num (base : Z) (t : Z -> ascii) (d : Z -> bv 8%N) (n : Z) (m : Z) := ∀(i : Z), n ≤ i ∧ i < m -> bv_signed (d i) = text_to_num base (t i).
