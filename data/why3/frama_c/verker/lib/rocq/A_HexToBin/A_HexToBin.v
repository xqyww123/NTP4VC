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
Open Scope Z_scope.
Axiom l_hex_to_bin : Z -> Z.
Axiom Q_A0 : l_hex_to_bin 48%Z = 0%Z.
Axiom Q_A1 : l_hex_to_bin 49%Z = 1%Z.
Axiom Q_A2 : l_hex_to_bin 50%Z = 2%Z.
Axiom Q_A3 : l_hex_to_bin 51%Z = 3%Z.
Axiom Q_A4 : l_hex_to_bin 52%Z = 4%Z.
Axiom Q_A5 : l_hex_to_bin 53%Z = 5%Z.
Axiom Q_A6 : l_hex_to_bin 54%Z = 6%Z.
Axiom Q_A7 : l_hex_to_bin 55%Z = 7%Z.
Axiom Q_A8 : l_hex_to_bin 56%Z = 8%Z.
Axiom Q_A9 : l_hex_to_bin 57%Z = 9%Z.
Axiom Q_AA : l_hex_to_bin 65%Z = 10%Z ∧ l_hex_to_bin 97%Z = l_hex_to_bin 65%Z.
Axiom Q_AB : l_hex_to_bin 66%Z = 11%Z ∧ l_hex_to_bin 98%Z = l_hex_to_bin 66%Z.
Axiom Q_AC : l_hex_to_bin 67%Z = 12%Z ∧ l_hex_to_bin 99%Z = l_hex_to_bin 67%Z.
Axiom Q_AD : l_hex_to_bin 68%Z = 13%Z ∧ l_hex_to_bin 100%Z = l_hex_to_bin 68%Z.
Axiom Q_AE : l_hex_to_bin 69%Z = 14%Z ∧ l_hex_to_bin 101%Z = l_hex_to_bin 69%Z.
Axiom Q_AF : l_hex_to_bin 70%Z = 15%Z ∧ l_hex_to_bin 102%Z = l_hex_to_bin 70%Z.
