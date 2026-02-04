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
Require Import prover.BacktrackArray.Types.
Require Import prover.Functions.Config.
Require Import prover.Functions.Func.
Require Import prover.Predicates.Pred.
Require Import prover.Choice.Choice.
Open Scope Z_scope.
Axiom func_of_array : forall {α : Type} `{Inhabited α}, list α -> α -> Z -> α.
Axiom func_of_array_def : forall  {α : Type} `{Inhabited α} (a : list α) (def1 : α) (x : Z), func_of_array a def1 x = (if decide (0%Z ≤ x ∧ x < Z.of_nat (length a)) then nth_i a x else def1).
Definition current_timestamp {α : Type} `{Inhabited α} (x : t α) : timestamp α := timestamp'mk (current_time x) (Z.of_nat (length (buffer x))) (func_of_array (buffer x) ([] : list α)).
Definition correct_table {α : Type} `{Inhabited α} (sz : Z) (b : Z -> list α) := ∀(x : Z), sz ≤ x ∨ x < 0%Z -> b x = ([] : list α).
Definition pop {α : Type} `{Inhabited α} (l : list α) : list α := match l with | [] => (default : list α) | cons x_x q => q end.
Program Fixpoint unroll {α : Type} `{Inhabited α} (tm : Z) (t0 : Z) (h : list Z) (b : Z -> list α) (sz : Z) : timestamp α :=
if decide (tm = 0%Z) then timestamp'mk t0 sz b else match h with | [] => timestamp'mk (t0 + tm) sz b | cons x q => (if decide (x = - 1%Z) then unroll (tm - 1%Z) t0 q b (Z.rem sz 2%Z) else unroll (tm - 1%Z) t0 q (update b x (pop (b x))) sz) end.
Admit Obligations.
Program Fixpoint unroll_correct {α : Type} `{Inhabited α} (tm : Z) (h : list Z) (b : Z -> list α) (sz : Z) : Prop :=
match h with | [] => tm = 0%Z | cons x q => (if decide (x = - 1%Z) then let s0 : Z := Z.rem sz 2%Z in s0 * 2%Z = sz ∧ unroll_correct (tm - 1%Z) q b s0 ∧ (∀(i : Z), s0 ≤ i ∨ i < 0%Z -> b i = ([] : list α)) else ¬ b x = ([] : list α) ∧ (0%Z ≤ x ∧ x < sz) ∧ unroll_correct (tm - 1%Z) q (update b x (pop (b x))) sz) end.
Admit Obligations.
Definition past_time {α : Type} `{Inhabited α} (t : timestamp α) (tb : Types.t α) := time t ≤ current_time tb ∧ unroll (current_time tb - time t) (time t) (history tb) (func_of_array (buffer tb) ([] : list α)) (Z.of_nat (length (buffer tb))) = t.
Definition precede {α : Type} `{Inhabited α} (tb1 : Types.t α) (tb2 : Types.t α) := ∀(t : timestamp α), past_time t tb1 -> past_time t tb2.
Definition before {α : Type} `{Inhabited α} (t1 : timestamp α) (t2 : timestamp α) := time t1 ≤ time t2.
Program Fixpoint list_forall {α : Type} `{Inhabited α} (p : α -> bool) (l : list α) : Prop :=
match l with | [] => True | cons x q => p x = true ∧ list_forall p q end.
Admit Obligations.
Definition correct {α : Type} `{Inhabited α} (tb : Types.t α) := (∀(t : timestamp α), past_time t tb -> 0%Z < Types.size t) ∧ (∀(t : timestamp α) (i : Z), past_time t tb ∧ 0%Z ≤ i -> list_forall (inv tb) (table t i)) ∧ (∀(t : timestamp α), past_time t tb -> correct_table (Types.size t) (table t)) ∧ unroll_correct (current_time tb) (history tb) (func_of_array (buffer tb) ([] : list α)) (Z.of_nat (length (buffer tb))).
Definition backtrack_to {α : Type} `{Inhabited α} (tbold : t α) (tbinter : t α) (tbnew : t α) := (∀(tm : timestamp α), past_time tm tbold -> past_time tm tbinter ∧ time tm ≤ time (current_timestamp tbold) ∧ time tm ≤ time (current_timestamp tbnew) ∧ before tm (current_timestamp tbnew) ∧ past_time tm tbnew) ∧ (∀(tm : timestamp α), past_time tm tbold -> past_time tm tbnew) ∧ precede tbold tbnew.
