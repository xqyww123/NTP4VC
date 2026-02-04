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
Open Scope Z_scope.
Axiom program_var : Type.
Axiom program_var_inhabited : Inhabited program_var.
Global Existing Instance program_var_inhabited.
Axiom program_var_countable : Countable program_var.
Global Existing Instance program_var_countable.
Inductive expr :=
  | Elit : Z -> expr
  | Evar : program_var -> expr
  | Esub : expr -> expr -> expr.
Axiom expr_inhabited : Inhabited expr.
Global Existing Instance expr_inhabited.
Axiom expr_countable : Countable expr.
Global Existing Instance expr_countable.
Inductive cmd :=
  | Cskip : cmd
  | Cassign : program_var -> expr -> cmd
  | Cseq : cmd -> cmd -> cmd
  | Cif : expr -> cmd -> cmd -> cmd
  | Cwhile : expr -> cmd -> cmd.
Axiom cmd_inhabited : Inhabited cmd.
Global Existing Instance cmd_inhabited.
Axiom cmd_countable : Countable cmd.
Global Existing Instance cmd_countable.
