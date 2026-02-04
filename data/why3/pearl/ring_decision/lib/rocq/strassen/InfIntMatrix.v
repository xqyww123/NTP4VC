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
Require Import Why3.int.Sum.
Require Import ring_decision.strassen.Sum_extended.
Require Import ring_decision.strassen.MaxFun.
Open Scope Z_scope.
Axiom infix_pl : Z -> Z -> Z.
Axiom prefix_mn : Z -> Z.
Axiom infix_as : Z -> Z -> Z.
Axiom Assoc : forall  (x : Z) (y : Z) (z : Z), infix_pl (infix_pl x y) z = infix_pl x (infix_pl y z).
Axiom Unit_def_l : forall  (x : Z), infix_pl 0%Z x = x.
Axiom Unit_def_r : forall  (x : Z), infix_pl x 0%Z = x.
Axiom Inv_def_l : forall  (x : Z), infix_pl (prefix_mn x) x = 0%Z.
Axiom Inv_def_r : forall  (x : Z), infix_pl x (prefix_mn x) = 0%Z.
Axiom Comm : forall  (x : Z) (y : Z), infix_pl x y = infix_pl y x.
Axiom Assoc1 : forall  (x : Z) (y : Z) (z : Z), infix_as (infix_as x y) z = infix_as x (infix_as y z).
Axiom Mul_distr_l : forall  (x : Z) (y : Z) (z : Z), infix_as x (infix_pl y z) = infix_pl (infix_as x y) (infix_as x z).
Axiom Mul_distr_r : forall  (y : Z) (z : Z) (x : Z), infix_as (infix_pl y z) x = infix_pl (infix_as y x) (infix_as z x).
Axiom Comm1 : forall  (x : Z) (y : Z), infix_as x y = infix_as y x.
Axiom one : Z.
Axiom Unitary : forall  (x : Z), infix_as one x = x.
Axiom NonTrivialRing : ¬ 0%Z = one.
Axiom mat : Type.
Axiom mat_inhabited : Inhabited mat.
Global Existing Instance mat_inhabited.
Axiom mat_countable : Countable mat.
Global Existing Instance mat_countable.
Axiom get : mat -> Z -> Z -> Z.
Axiom row_zeros : mat -> Z -> Z.
Axiom col_zeros : mat -> Z -> Z.
Axiom create : (Z -> Z) -> (Z -> Z) -> (Z -> Z -> Z) -> mat.
Axiom create_rowz : forall  (i : Z) (rz : Z -> Z) (cz : Z -> Z) (f : Z -> Z -> Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ rz i), row_zeros (create rz cz f) i = rz i.
Axiom create_colz : forall  (j : Z) (cz : Z -> Z) (rz : Z -> Z) (f : Z -> Z -> Z) (fact0 : 0%Z ≤ j) (fact1 : 0%Z ≤ cz j), col_zeros (create rz cz f) j = cz j.
Axiom create_get_ib : forall  (i : Z) (cz : Z -> Z) (j : Z) (rz : Z -> Z) (f : Z -> Z -> Z) (fact0 : 0%Z ≤ i) (fact1 : i < cz j) (fact2 : 0%Z ≤ j) (fact3 : j < rz i), get (create rz cz f) i j = f i j.
Axiom create_get_oob : forall  (i : Z) (j : Z) (cz : Z -> Z) (rz : Z -> Z) (f : Z -> Z -> Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : cz j ≤ i ∨ rz i ≤ j), get (create rz cz f) i j = 0%Z.
Axiom result : mat -> Z -> Z -> Z -> Z.
Axiom result1 : mat -> Z -> Z -> Z -> Z.
Axiom result2 : mat -> Z -> Z -> Z -> Z -> Z -> Z.
Axiom result'def : forall  (m : mat) (i : Z) (j : Z) (i1 : Z), result m i j i1 = (if decide (i1 = i) then Z.max (j + 1%Z) (row_zeros m i) else row_zeros m i1).
Axiom result'def1 : forall  (m : mat) (i : Z) (j : Z) (j1 : Z), result1 m i j j1 = (if decide (j1 = j) then Z.max (i + 1%Z) (col_zeros m j) else col_zeros m j1).
Axiom result'def2 : forall  (m : mat) (i : Z) (j : Z) (v : Z) (i1 : Z) (j1 : Z), result2 m i j v i1 j1 = (if decide (i1 = i ∧ j1 = j) then v else get m i1 j1).
Definition set (m : mat) (i : Z) (j : Z) (v : Z) : mat := if decide (0%Z ≤ i ∧ 0%Z ≤ j) then create (result m i j) (result1 m i j) (result2 m i j v) else m.
Axiom zero : Z.
Axiom infix_pl' : Z -> Z -> Z.
Axiom prefix_mn' : Z -> Z.
Axiom infix_as' : Z -> Z -> Z.
Axiom Assoc2 : forall  (x : Z) (y : Z) (z : Z), infix_pl' (infix_pl' x y) z = infix_pl' x (infix_pl' y z).
Axiom Unit_def_l1 : forall  (x : Z), infix_pl' zero x = x.
Axiom Unit_def_r1 : forall  (x : Z), infix_pl' x zero = x.
Axiom Inv_def_l1 : forall  (x : Z), infix_pl' (prefix_mn' x) x = zero.
Axiom Inv_def_r1 : forall  (x : Z), infix_pl' x (prefix_mn' x) = zero.
Axiom Comm2 : forall  (x : Z) (y : Z), infix_pl' x y = infix_pl' y x.
Axiom Assoc3 : forall  (x : Z) (y : Z) (z : Z), infix_as' (infix_as' x y) z = infix_as' x (infix_as' y z).
Axiom Mul_distr_l1 : forall  (x : Z) (y : Z) (z : Z), infix_as' x (infix_pl' y z) = infix_pl' (infix_as' x y) (infix_as' x z).
Axiom Mul_distr_r1 : forall  (y : Z) (z : Z) (x : Z), infix_as' (infix_pl' y z) x = infix_pl' (infix_as' y x) (infix_as' z x).
Axiom Comm3 : forall  (x : Z) (y : Z), infix_as' x y = infix_as' y x.
Axiom one1 : Z.
Axiom Unitary1 : forall  (x : Z), infix_as' one1 x = x.
Axiom NonTrivialRing1 : ¬ zero = one1.
Axiom row_zeros_def : forall  (i : Z) (m : mat) (j : Z) (fact0 : 0%Z ≤ i) (fact1 : row_zeros m i ≤ j), get m i j = zero.
Axiom col_zeros_def : forall  (j : Z) (m : mat) (i : Z) (fact0 : 0%Z ≤ j) (fact1 : col_zeros m j ≤ i), get m i j = zero.
Axiom row_zeros_nonneg : forall  (i : Z) (m : mat) (fact0 : 0%Z ≤ i), 0%Z ≤ row_zeros m i.
Axiom col_zeros_nonneg : forall  (j : Z) (m : mat) (fact0 : 0%Z ≤ j), 0%Z ≤ col_zeros m j.
Axiom set_def_changed : forall  (i : Z) (j : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j), get (set m i j v) i j = v.
Axiom set_def_unchanged : forall  (i : Z) (j : Z) (i' : Z) (j' : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ i') (fact3 : 0%Z ≤ j') (fact4 : ¬ i = i' ∨ ¬ j = j'), get (set m i j v) i' j' = get m i' j'.
Axiom set_def_rowz_changed : forall  (i : Z) (j : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : row_zeros m i ≤ j), row_zeros (set m i j v) i = j + 1%Z.
Axiom set_def_colz_changed : forall  (i : Z) (j : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : col_zeros m j ≤ i), col_zeros (set m i j v) j = i + 1%Z.
Axiom set_def_rowz_unchanged : forall  (i : Z) (j : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : j < row_zeros m i), row_zeros (set m i j v) i = row_zeros m i.
Axiom set_def_colz_unchanged : forall  (i : Z) (j : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : i < col_zeros m j), col_zeros (set m i j v) j = col_zeros m j.
Axiom set_def_other_rowz : forall  (i : Z) (j : Z) (i' : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ i') (fact3 : ¬ i = i'), row_zeros (set m i j v) i' = row_zeros m i'.
Axiom set_def_other_colz : forall  (i : Z) (j : Z) (j' : Z) (m : mat) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : 0%Z ≤ j) (fact2 : 0%Z ≤ j') (fact3 : ¬ j = j'), col_zeros (set m i j v) j' = col_zeros m j'.
Definition infix_eqeq (m1 : mat) (m2 : mat) := ∀(i : Z) (j : Z), 0%Z ≤ i -> 0%Z ≤ j -> get m1 i j = get m2 i j.
Axiom extensionality : forall  (m1 : mat) (m2 : mat) (fact0 : infix_eqeq m1 m2), m1 = m2.
Definition infix_eqeqeq (m1 : mat) (m2 : mat) := ∀(i : Z) (j : Z), 0%Z ≤ i -> 0%Z ≤ j -> row_zeros m1 i = row_zeros m2 i ∧ col_zeros m1 j = col_zeros m2 j.
Definition in_bounds (m : mat) (i : Z) (j : Z) := (0%Z ≤ i ∧ i < col_zeros m j) ∧ 0%Z ≤ j ∧ j < row_zeros m i.
Definition size (m : mat) (r : Z) (c : Z) := (∀(i : Z), 0%Z ≤ i -> row_zeros m i = c) ∧ (∀(j : Z), 0%Z ≤ j -> col_zeros m j = r).
Axiom result3 : Z -> Z -> Z.
Axiom result4 : Z -> Z -> Z.
Axiom result'def3 : forall  (c : Z) (x : Z), result3 c x = Z.max 0%Z c.
Axiom result'def4 : forall  (r : Z) (x : Z), result4 r x = Z.max 0%Z r.
Definition fcreate (r : Z) (c : Z) (f : Z -> Z -> Z) : mat := create (result3 c) (result4 r) f.
Axiom fc : Z -> Z -> Z.
Axiom fc'def : forall  (y0 : Z) (y1 : Z), fc y0 y1 = 0%Z.
Definition mzero : mat := fcreate 0%Z 0%Z fc.
Axiom fc1 : Z -> Z -> Z.
Axiom fc'def1 : forall  (y0 : Z) (y1 : Z), fc1 y0 y1 = 0%Z.
Definition zerorc (r : Z) (c : Z) : mat := fcreate r c fc1.
Definition idf (x : Z) (y : Z) : Z := if decide (x = y) then 1%Z else 0%Z.
Axiom result5 : Z -> Z.
Axiom result6 : Z -> Z.
Axiom idf_closure : Z -> Z -> Z.
Axiom result'def5 : forall  (i : Z), result5 i = i + 1%Z.
Axiom result'def6 : forall  (j : Z), result6 j = j + 1%Z.
Axiom idf_closure_def : forall  (y : Z) (y1 : Z), idf_closure y y1 = idf y y1.
Definition id1 : mat := create result5 result6 idf_closure.
Definition idrc (r : Z) (c : Z) : mat := fcreate r c idf_closure.
Axiom add2f : mat -> mat -> Z -> Z -> Z.
Axiom add2f'def : forall  (a : mat) (b : mat) (x : Z) (y : Z), add2f a b x y = get a x y + get b x y.
Axiom fc2 : mat -> mat -> Z -> Z.
Axiom fc3 : mat -> mat -> Z -> Z.
Axiom fc'def2 : forall  (a : mat) (b : mat) (i : Z), fc2 a b i = Z.max (row_zeros a i) (row_zeros b i).
Axiom fc'def3 : forall  (a : mat) (b : mat) (j : Z), fc3 a b j = Z.max (col_zeros a j) (col_zeros b j).
Definition f_add (a : mat) (b : mat) : mat := create (fc2 a b) (fc3 a b) (add2f a b).
Axiom add : mat -> mat -> mat.
Axiom add'spec : forall  (a : mat) (b : mat), add a b = f_add a b.
Axiom opp2f : mat -> Z -> Z -> Z.
Axiom opp2f'def : forall  (a : mat) (x : Z) (y : Z), opp2f a x y = - get a x y.
Axiom row_zeros_closure : mat -> Z -> Z.
Axiom col_zeros_closure : mat -> Z -> Z.
Axiom row_zeros_closure_def : forall  (y : mat) (y1 : Z), row_zeros_closure y y1 = row_zeros y y1.
Axiom col_zeros_closure_def : forall  (y : mat) (y1 : Z), col_zeros_closure y y1 = col_zeros y y1.
Definition f_opp (a : mat) : mat := create (row_zeros_closure a) (col_zeros_closure a) (opp2f a).
Axiom opp : mat -> mat.
Axiom opp'spec : forall  (a : mat), opp a = f_opp a.
Definition sub (a : mat) (b : mat) : mat := add a (opp b).
Axiom mul_atom : mat -> mat -> Z -> Z -> Z -> Z.
Axiom mul_atom'def : forall  (a : mat) (b : mat) (i : Z) (j : Z) (k : Z), mul_atom a b i j k = get a i k * get b k j.
Definition mul_cell_bound (a : mat) (b : mat) (i : Z) (j : Z) : Z := Z.min (row_zeros a i) (col_zeros b j).
Axiom mul_cell : mat -> mat -> Z -> Z -> Z.
Axiom mul_cell'def : forall  (a : mat) (b : mat) (i : Z) (j : Z), mul_cell a b i j = sum (mul_atom a b i j) 0%Z (mul_cell_bound a b i j).
Axiom fc4 : mat -> mat -> Z -> Z.
Axiom fc5 : mat -> mat -> Z -> Z.
Axiom fc'def4 : forall  (a : mat) (b : mat) (i : Z), fc4 a b i = maxf (row_zeros_closure b) 0%Z (row_zeros a i).
Axiom fc'def5 : forall  (a : mat) (b : mat) (j : Z), fc5 a b j = maxf (col_zeros_closure a) 0%Z (col_zeros b j).
Definition f_mul (a : mat) (b : mat) : mat := create (fc4 a b) (fc5 a b) (mul_cell a b).
Axiom mul : mat -> mat -> mat.
Axiom mul'spec : forall  (a : mat) (b : mat), mul a b = f_mul a b.
Axiom ft1 : mat -> mat -> mat -> Z -> Z -> Z -> Z -> Z.
Axiom ft1'def : forall  (a : mat) (b : mat) (c : mat) (i : Z) (j : Z) (k : Z), ft1 a b c i j k = smulf (mul_atom a b i k) (get c k j).
Axiom ft2 : mat -> mat -> mat -> Z -> Z -> Z -> Z -> Z.
Axiom ft2'def : forall  (a : mat) (b : mat) (c : mat) (i : Z) (j : Z) (k : Z), ft2 a b c i j k = smulf (mul_atom b c k j) (get a i k).
Axiom extf : Z -> mat -> Z -> Z -> Z.
Axiom extf'def : forall  (c : Z) (a : mat) (x : Z) (y : Z), extf c a x y = c * get a x y.
Definition f_extp (c : Z) (a : mat) : mat := create (row_zeros_closure a) (col_zeros_closure a) (extf c a).
Axiom extp : Z -> mat -> mat.
Axiom extp'spec : forall  (c : Z) (a : mat), extp c a = f_extp c a.
