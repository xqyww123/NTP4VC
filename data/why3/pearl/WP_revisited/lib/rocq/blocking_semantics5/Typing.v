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
Require Import WP_revisited.blocking_semantics5.Syntax.
Open Scope Z_scope.
Definition type_value (v : value) : datatype := match v with | Vvoid => TYunit | Vint _ => TYint | Vbool _ => TYbool end.
Inductive type_operator : operator -> datatype -> datatype -> datatype -> Prop :=
 | Type_plus : type_operator Oplus TYint TYint TYint
 | Type_minus : type_operator Ominus TYint TYint TYint
 | Type_mult : type_operator Omult TYint TYint TYint
 | Type_le : type_operator Ole TYint TYint TYbool.
Axiom type_stack : Type.
Axiom type_stack_inhabited : Inhabited type_stack.
Global Existing Instance type_stack_inhabited.
Axiom type_stack_countable : Countable type_stack.
Global Existing Instance type_stack_countable.
Program Fixpoint get_vartype (i : ident) (pi : list (ident * datatype)) : datatype :=
match pi with | [] => TYunit | cons (x, ty) r => (if decide (x = i) then ty else get_vartype i r) end.
Admit Obligations.
Axiom type_env : Type.
Axiom type_env_inhabited : Inhabited type_env.
Global Existing Instance type_env_inhabited.
Axiom type_env_countable : Countable type_env.
Global Existing Instance type_env_countable.
Inductive type_term : (mident -> datatype) -> list (ident * datatype) -> term -> datatype -> Prop :=
 | Type_value (sigma : mident -> datatype) (pi : list (ident * datatype)) (v : value) : type_term sigma pi (Tvalue v) (type_value v)
 | Type_var (v : ident) (pi : list (ident * datatype)) (ty : datatype) (sigma : mident -> datatype) : get_vartype v pi = ty -> type_term sigma pi (Tvar v) ty
 | Type_deref (sigma : mident -> datatype) (v : mident) (ty : datatype) (pi : list (ident * datatype)) : sigma v = ty -> type_term sigma pi (Tderef v) ty
 | Type_bin (sigma : mident -> datatype) (pi : list (ident * datatype)) (t1 : term) (ty1 : datatype) (t2 : term) (ty2 : datatype) (op : operator) (ty : datatype) : type_term sigma pi t1 ty1 -> type_term sigma pi t2 ty2 -> type_operator op ty1 ty2 ty -> type_term sigma pi (Tbin t1 op t2) ty.
Inductive type_fmla : (mident -> datatype) -> list (ident * datatype) -> fmla -> Prop :=
 | Type_term (sigma : mident -> datatype) (pi : list (ident * datatype)) (t : term) : type_term sigma pi t TYbool -> type_fmla sigma pi (Fterm t)
 | Type_conj (sigma : mident -> datatype) (pi : list (ident * datatype)) (f1 : fmla) (f2 : fmla) : type_fmla sigma pi f1 -> type_fmla sigma pi f2 -> type_fmla sigma pi (Fand f1 f2)
 | Type_neg (sigma : mident -> datatype) (pi : list (ident * datatype)) (f : fmla) : type_fmla sigma pi f -> type_fmla sigma pi (Fnot f)
 | Type_implies (sigma : mident -> datatype) (pi : list (ident * datatype)) (f1 : fmla) (f2 : fmla) : type_fmla sigma pi f1 -> type_fmla sigma pi f2 -> type_fmla sigma pi (Fimplies f1 f2)
 | Type_let (sigma : mident -> datatype) (pi : list (ident * datatype)) (t : term) (ty : datatype) (x : ident) (f : fmla) : type_term sigma pi t ty -> type_fmla sigma (cons (x, ty) pi) f -> type_fmla sigma pi (Flet x t f)
 | Type_forall (sigma : mident -> datatype) (x : ident) (ty : datatype) (pi : list (ident * datatype)) (f : fmla) : type_fmla sigma (cons (x, ty) pi) f -> type_fmla sigma pi (Fforall x ty f).
Inductive type_stmt : (mident -> datatype) -> list (ident * datatype) -> stmt -> Prop :=
 | Type_skip (sigma : mident -> datatype) (pi : list (ident * datatype)) : type_stmt sigma pi Sskip
 | Type_seq (sigma : mident -> datatype) (pi : list (ident * datatype)) (s1 : stmt) (s2 : stmt) : type_stmt sigma pi s1 -> type_stmt sigma pi s2 -> type_stmt sigma pi (Sseq s1 s2)
 | Type_assigns (sigma : mident -> datatype) (x : mident) (ty : datatype) (pi : list (ident * datatype)) (t : term) : sigma x = ty -> type_term sigma pi t ty -> type_stmt sigma pi (Sassign x t)
 | Type_if (sigma : mident -> datatype) (pi : list (ident * datatype)) (t : term) (s1 : stmt) (s2 : stmt) : type_term sigma pi t TYbool -> type_stmt sigma pi s1 -> type_stmt sigma pi s2 -> type_stmt sigma pi (Sif t s1 s2)
 | Type_assert (sigma : mident -> datatype) (pi : list (ident * datatype)) (p : fmla) : type_fmla sigma pi p -> type_stmt sigma pi (Sassert p)
 | Type_while (sigma : mident -> datatype) (pi : list (ident * datatype)) (inv : fmla) (cond : term) (body : stmt) : type_fmla sigma pi inv -> type_term sigma pi cond TYbool -> type_stmt sigma pi body -> type_stmt sigma pi (Swhile cond inv body).
