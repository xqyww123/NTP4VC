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
Inductive datatype :=
  | TYunit : datatype
  | TYint : datatype
  | TYbool : datatype.
Axiom datatype_inhabited : Inhabited datatype.
Global Existing Instance datatype_inhabited.
Axiom datatype_countable : Countable datatype.
Global Existing Instance datatype_countable.
Inductive value :=
  | Vvoid : value
  | Vint : Z -> value
  | Vbool : bool -> value.
Axiom value_inhabited : Inhabited value.
Global Existing Instance value_inhabited.
Axiom value_countable : Countable value.
Global Existing Instance value_countable.
Inductive operator :=
  | Oplus : operator
  | Ominus : operator
  | Omult : operator
  | Ole : operator.
Axiom operator_inhabited : Inhabited operator.
Global Existing Instance operator_inhabited.
Axiom operator_countable : Countable operator.
Global Existing Instance operator_countable.
Axiom mident : Type.
Axiom mident_inhabited : Inhabited mident.
Global Existing Instance mident_inhabited.
Axiom mident_countable : Countable mident.
Global Existing Instance mident_countable.
Axiom ident : Type.
Axiom ident_inhabited : Inhabited ident.
Global Existing Instance ident_inhabited.
Axiom ident_countable : Countable ident.
Global Existing Instance ident_countable.
Inductive term :=
  | Tvalue : value -> term
  | Tvar : ident -> term
  | Tderef : mident -> term
  | Tbin : term -> operator -> term -> term.
Axiom term_inhabited : Inhabited term.
Global Existing Instance term_inhabited.
Axiom term_countable : Countable term.
Global Existing Instance term_countable.
Inductive fmla :=
  | Fterm : term -> fmla
  | Fand : fmla -> fmla -> fmla
  | Fnot : fmla -> fmla
  | Fimplies : fmla -> fmla -> fmla
  | Flet : ident -> term -> fmla -> fmla
  | Fforall : ident -> datatype -> fmla -> fmla.
Axiom fmla_inhabited : Inhabited fmla.
Global Existing Instance fmla_inhabited.
Axiom fmla_countable : Countable fmla.
Global Existing Instance fmla_countable.
Inductive stmt :=
  | Sskip : stmt
  | Sassign : mident -> term -> stmt
  | Sseq : stmt -> stmt -> stmt
  | Sif : term -> stmt -> stmt -> stmt
  | Sassert : fmla -> stmt
  | Swhile : term -> fmla -> stmt -> stmt.
Axiom stmt_inhabited : Inhabited stmt.
Global Existing Instance stmt_inhabited.
Axiom stmt_countable : Countable stmt.
Global Existing Instance stmt_countable.
