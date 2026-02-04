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
Definition p_islower (c : Z) := 97%Z ≤ c ∧ c ≤ 122%Z.
Definition p_isupper (c : Z) := 65%Z ≤ c ∧ c ≤ 90%Z.
Definition p_isalpha (c : Z) := p_islower c ∨ p_isupper c.
Definition p_isdigit (c : Z) := 48%Z ≤ c ∧ c ≤ 57%Z.
Definition p_isodigit (c : Z) := 48%Z ≤ c ∧ c ≤ 55%Z.
Definition p_isalnum (c : Z) := p_isalpha c ∨ p_isdigit c.
Definition p_isspace (c : Z) := c = 9%Z ∨ c = 10%Z ∨ c = 12%Z ∨ c = 13%Z ∨ c = 32%Z.
Definition p_isxdigit (c : Z) := p_isdigit c ∨ 65%Z ≤ c ∧ c ≤ 70%Z ∨ 97%Z ≤ c ∧ c ≤ 102%Z.
Axiom l_tolower : Z -> Z.
Axiom l_toupper : Z -> Z.
Axiom Q_a : l_tolower 65%Z = 97%Z.
Axiom Q_b : l_tolower 66%Z = 98%Z.
Axiom Q_c : l_tolower 67%Z = 99%Z.
Axiom Q_d : l_tolower 68%Z = 100%Z.
Axiom Q_e : l_tolower 69%Z = 101%Z.
Axiom Q_f : l_tolower 70%Z = 102%Z.
Axiom Q_g : l_tolower 71%Z = 103%Z.
Axiom Q_h : l_tolower 72%Z = 104%Z.
Axiom Q_i : l_tolower 73%Z = 105%Z.
Axiom Q_j : l_tolower 74%Z = 106%Z.
Axiom Q_k : l_tolower 75%Z = 107%Z.
Axiom Q_l : l_tolower 76%Z = 108%Z.
Axiom Q_m : l_tolower 77%Z = 109%Z.
Axiom Q_n : l_tolower 78%Z = 110%Z.
Axiom Q_o : l_tolower 79%Z = 111%Z.
Axiom Q_p : l_tolower 80%Z = 112%Z.
Axiom Q_q : l_tolower 81%Z = 113%Z.
Axiom Q_r : l_tolower 82%Z = 114%Z.
Axiom Q_s : l_tolower 83%Z = 115%Z.
Axiom Q_t : l_tolower 84%Z = 116%Z.
Axiom Q_u : l_tolower 85%Z = 117%Z.
Axiom Q_v : l_tolower 86%Z = 118%Z.
Axiom Q_w : l_tolower 87%Z = 119%Z.
Axiom Q_x : l_tolower 88%Z = 120%Z.
Axiom Q_y : l_tolower 89%Z = 121%Z.
Axiom Q_z : l_tolower 90%Z = 122%Z.
Axiom Q_pl : forall  (c : Z) (fact0 : ¬ p_isupper c), l_tolower c = c.
Axiom Q_pu : forall  (c : Z) (fact0 : ¬ p_islower c), l_toupper c = c.
Axiom Q_tl : forall  (c : Z) (fact0 : ¬ p_islower c), l_toupper (l_tolower c) = c.
Axiom Q_tu : forall  (c : Z) (fact0 : ¬ p_isupper c), l_tolower (l_toupper c) = c.
