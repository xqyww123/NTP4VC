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
From Stdlib Require Import Logic.ClassicalEpsilon.

#[global]
Instance classical_eq_decision_all (A : Type) : EqDecision A :=
  fun x y => excluded_middle_informative (x = y).

#[global]
Instance classical_decision_all (A : Prop) : Decision A :=
  excluded_middle_informative A.

Global Instance ascii_inhabited : Inhabited ascii := populate (ascii_of_nat 0%nat).

Open Scope Z_scope.

Notation take_i := (fun i l => take (Z.to_nat i) l) (only parsing).
Notation drop_i := (fun i l => drop (Z.to_nat i) l) (only parsing).
Notation length_i := (fun l => Z.to_nat (length l)) (only parsing).
Notation nth_error_i := (fun l i => nth_error l (Z.to_nat i)) (only parsing).
Notation nth_i := (fun l i => nth (Z.to_nat i) l inhabitant) (only parsing).
Notation replicate_i := (fun i l => replicate (Z.to_nat i) l) (only parsing).

Definition slice {α : Type} (l : list α) (i j : nat) : list α :=
  take (j - i) (drop i l).
Definition slice_i {α : Type} (l : list α) (i j : Z) : list α :=
  take ((Z.to_nat j) - (Z.to_nat i)) (drop (Z.to_nat i) l).

Transparent slice_i slice.

Notation int'16_max  := (32767%bv : bv 16%N) (only parsing).
Notation int'16_min  := ((-32768)%bv : bv 16%N) (only parsing).
Notation int'31_max  := (1073741823%bv : bv 31%N) (only parsing).
Notation int'31_min  := ((-1073741824)%bv : bv 31%N) (only parsing).
Notation int'32_max  := (2147483647%bv : bv 32%N) (only parsing).
Notation int'32_min  := ((-2147483648)%bv : bv 32%N) (only parsing).
Notation int'63_max  := (4611686018427387903%bv : bv 63%N) (only parsing).
Notation int'63_min  := ((-4611686018427387904)%bv : bv 63%N) (only parsing).
Notation int'64_max  := (9223372036854775807%bv : bv 64%N) (only parsing).
Notation int'64_min  := ((-9223372036854775808)%bv : bv 64%N) (only parsing).
Notation uint'16_max := (65535%bv : bv 16%N) (only parsing).
Notation uint'16_min := (0%bv : bv 16%N) (only parsing).
Notation uint'31_max := (2147483647%bv : bv 31%N) (only parsing).
Notation uint'31_min := (0%bv : bv 31%N) (only parsing).
Notation uint'32_max := (4294967295%bv : bv 32%N) (only parsing).
Notation uint'32_min := (0%bv : bv 32%N) (only parsing).
Notation uint'63_max := (9223372036854775807%bv : bv 63) (only parsing).
Notation uint'63_min := (0%bv : bv 63%N) (only parsing).
Notation uint'64_max := (18446744073709551615%bv : bv 64%N) (only parsing).
Notation uint'64_min := (0%bv : bv 64%N) (only parsing).

Notation int'16_in_bounds  := (fun x => (bv_signed int'16_min ≤ x ∧ x ≤ bv_signed int'16_max)%Z) (only parsing).
Notation int'31_in_bounds  := (fun x => (bv_signed int'31_min ≤ x ∧ x ≤ bv_signed int'31_max)%Z) (only parsing).
Notation int'32_in_bounds  := (fun x => (bv_signed int'32_min ≤ x ∧ x ≤ bv_signed int'32_max)%Z) (only parsing).
Notation int'63_in_bounds  := (fun x => (bv_signed int'63_min ≤ x ∧ x ≤ bv_signed int'63_max)%Z) (only parsing).
Notation int'64_in_bounds  := (fun x => (bv_signed int'64_min ≤ x ∧ x ≤ bv_signed int'64_max)%Z) (only parsing).
Notation uint'8_in_bounds  := (fun x => (0 ≤ x ∧ x ≤ 256)%Z) (only parsing).
Notation uint'16_in_bounds := (fun x => (0 ≤ x ∧ x ≤ bv_unsigned int'16_max)%Z) (only parsing).
Notation uint'31_in_bounds := (fun x => (0 ≤ x ∧ x ≤ bv_unsigned int'31_max)%Z) (only parsing).
Notation uint'32_in_bounds := (fun x => (0 ≤ x ∧ x ≤ bv_unsigned int'32_max)%Z) (only parsing).
Notation uint'63_in_bounds := (fun x => (0 ≤ x ∧ x ≤ bv_unsigned int'63_max)%Z) (only parsing).
Notation uint'64_in_bounds := (fun x => (0 ≤ x ∧ x ≤ bv_unsigned int'64_max)%Z) (only parsing).

Notation is_msb_set := (fun b => bool_decide (bv_signed b < 0)%Z) (only parsing).

Definition create_list   {A : Type} (n : nat) (f : nat -> A) := map f (seq 0%nat n).
Definition create_list_i {A : Type} (n : Z) (f : Z -> A) := map f (seqZ 0%Z n).

Definition map_occ_list {α : Type} (v : α) (m : Z -> α) (l u : Z) :=
    length (filter (fun n => bool_decide (m n = v)) (seqZ l (u - l))).

Notation map_occ_list_i := (fun v m l u => Z.of_nat (map_occ_list v m l u)) (only parsing).

Definition fun_updt {K V} (f : K -> V) (k : K) (v : V) := fn_insert k v f.

Axiom array31 : Type -> Type.
Axiom array32 : Type -> Type.
Axiom array63 : Type -> Type.

Axiom array31_elts : forall {α : Type}, Z -> α.
Axiom array32_elts : forall {α : Type}, array32 α -> Z -> α.
Axiom array63_elts : forall {α : Type}, array63 α -> list α.

Notation array63_nth := (fun a i => nth i (array63_elts a) inhabitant) (only parsing).

Axiom array31_length : forall {α : Type}, array31 α -> bv 31%N.
Axiom array32_length : forall {α : Type}, array32 α -> bv 32%N.
Axiom array63_length : forall {α : Type}, array63 α -> bv 63%N.

Notation set_list_i := (fun (l : list _) (i : Z) x => <[Z.to_nat i:=x]> l) (only parsing).
Notation set_list := (fun (l : list _) (i : nat) x => <[i:=x]> l) (only parsing).

Notation is_None := (fun x => x ≠ None) (only parsing).
Notation is_Nil := (fun x => x ≠ []) (only parsing).
Notation hd' := (fun l => hd inhabitant l) (only parsing).

Definition tl_error {A : Type} (l : list A) :=
  match l with | [] => None | _ :: l' => Some l' end.

Notation is_empty := (fun s => s = ∅) (only parsing).
Notation insert_set := (fun x S => S ∪ {[x]}) (only parsing).
Notation insert_mset := (fun x S => S ∪ {[+ x +]}) (only parsing).
Notation remove_set := (fun x S => S ∖ {[x]}) (only parsing).
Notation remove_mset := (fun x S => S ∖ {[+ x +]}) (only parsing).
Notation size_i := (fun S => Z.of_nat (size S)) (only parsing).
Notation filter' := (fun S P => filter P S) (only parsing).

Definition gset_pick_em `{Countable K, Inhabited K} (X : gset K) : K :=
   epsilon (inhabits inhabitant) (fun x => x ∈ X).

Definition propset_pick {K} `{Inhabited K} (X : propset K) : K :=
    epsilon (inhabits inhabitant) (fun x => x ∈ X).

Notation pow2 := (fun n => Z.pow 2%Z n) (only parsing).

Definition bv_slt {n} (x y : bv n) : bool := Z.ltb (bv_signed x) (bv_signed y).
Definition bv_sle {n} (x y : bv n) : bool := Z.leb (bv_signed x) (bv_signed y).
Definition bv_sgt {n} (x y : bv n) : bool := Z.gtb (bv_signed x) (bv_signed y).
Definition bv_sge {n} (x y : bv n) : bool := Z.geb (bv_signed x) (bv_signed y).
Definition bv_ult {n} (x y : bv n) : bool := Z.ltb (bv_unsigned x) (bv_unsigned y).
Definition bv_ule {n} (x y : bv n) : bool := Z.leb (bv_unsigned x) (bv_unsigned y).
Definition bv_ugt {n} (x y : bv n) : bool := Z.gtb (bv_unsigned x) (bv_unsigned y).
Definition bv_uge {n} (x y : bv n) : bool := Z.geb (bv_unsigned x) (bv_unsigned y).

Transparent bv_slt bv_sle bv_sgt bv_sge.
Transparent bv_ult bv_ule bv_ugt bv_uge.

Notation bv_testbit := (fun b i => Z.testbit (bv_unsigned b) i) (only parsing).
Notation bv_testbit_b := (fun b i => Z.testbit (bv_unsigned b) (bv_unsigned i)) (only parsing).

Definition eq_sub_bv {m : N} (a b : bv m) (i n : N) :=
  bv_extract i n a = bv_extract i n b.

Definition eq_sub_bv_n {m : N} (a b : bv m) (i n : nat) :=
  eq_sub_bv a b (N.of_nat i) (N.of_nat n).

Definition eq_sub_bv_z {m : N} (a b : bv m) (i n : Z) :=
  eq_sub_bv a b (Z.to_N i) (Z.to_N n).

Definition eq_sub_bv_b {m m1 m2 : N} (a b : bv m) (i : bv m1) (n : bv m2) :=
  eq_sub_bv_z a b (bv_unsigned i) (bv_unsigned n).

Transparent eq_sub_bv eq_sub_bv_z eq_sub_bv_n eq_sub_bv_b.

Notation Coprime_z := (fun a b => Z.eqb (Z.gcd a b) 1%Z) (only parsing).

Notation w8_size_bv := (8%bv : bv 8%N) (only parsing).
Notation w16_size_bv := (16%bv : bv 16%N) (only parsing).
Notation w32_size_bv := (32%bv : bv 32%N) (only parsing).
Notation w64_size_bv := (64%bv : bv 64%N) (only parsing).
Notation w128_size_bv := (128%bv : bv 128%N) (only parsing).
Notation w256_size_bv := (256%bv : bv 256%N) (only parsing).
Notation w8_size_i := 8%Z (only parsing).
Notation w16_size_i := 16%Z (only parsing).
Notation w32_size_i := 32%Z (only parsing).
Notation w64_size_i := 64%Z (only parsing).
Notation w128_size_i := 128%Z (only parsing).
Notation w256_size_i := 256%Z (only parsing).

Definition bv_rotl {n} (x : bv n) (k : Z) : bv n :=
    let k' := Z.modulo k (Z.of_N n) in
    bv_or (x ≪ Z_to_bv n k') (x ≫ Z_to_bv n (Z.of_N n - k')).

Definition bv_rotl_b {n} (x : bv n) (k : bv n) : bv n := bv_rotl x (bv_unsigned k).
  
Definition bv_rotr {n} (x : bv n) (k : Z) : bv n :=
    let k' := Z.modulo k (Z.of_N n) in
    bv_or (x ≫ Z_to_bv n k') (x ≪ Z_to_bv n (Z.of_N n - k')).

Definition bv_rotr_b {n} (x : bv n) (k : bv n) : bv n := bv_rotr x (bv_unsigned k).
  
Transparent bv_rotl bv_rotr bv_rotl_b bv_rotr_b.

Notation multiplicity_i := (fun x S => Z.of_nat (multiplicity x S)) (only parsing).

Notation set_comprehension := (fun (S : propset _) P => ({[ x | P x /\ x ∈ S ]} : propset _)) (only parsing).

Notation fmapsto := (fun k v (f : gmap _ _) => f !! k = Some v) (only parsing).

Notation ascii_code := (fun ascii => Z.of_nat (Ascii.nat_of_ascii ascii)) (only parsing).
Notation ascii_of_code := (fun code => Ascii.ascii_of_nat (Z.to_nat code)) (only parsing).

Definition str_contains (s2 s1 : string) : bool :=
    match index 0 s1 s2 with
    | Some _ => true
    | None => false
    end.

Transparent str_contains.

Notation get_str := (fun s i => from_option (fun x => x) (ascii_of_nat 0%nat) (String.get i s)) (only parsing).
Notation get_str_i := (fun s i => from_option (fun x => x) (ascii_of_nat 0%nat) (String.get (Z.to_nat i) s)) (only parsing).

Fixpoint string_repeat (n : nat) (c : ascii) : string :=
    match n with
    | O => EmptyString
    | S n' => String c (string_repeat n' c)
    end.
  
Notation string_repeat_i := (fun n c => string_repeat (Z.to_nat n) c) (only parsing).

Notation why3_substring := (fun s i n => substring i n s) (only parsing).

Notation gset_map := (fun f (S : gset _) => (set_map f S : gset _)).

Definition lookup_gmap_total {K A} `{Countable K} `{Inhabited A} (m : gmap K A) (k : K) : A := m !!! k.
Transparent lookup_gmap_total.

Definition insert_gmap {K A} `{Countable K} (k : K) (v : A) (m : gmap K A) := insert k v m.
Definition delete_gmap {K A} `{Countable K} (k : K) (m : gmap K A) := delete k m.

Transparent delete_gmap delete_gmap.

Global Instance R_inhabited : Inhabited R := populate R0.

 Definition gset_max (s : gset Z) : Z :=
    match elements s with
    | [] => 0%Z
    | x :: xs => set_fold Z.max x s
    end.

  (* For minimum element *)
  Definition gset_min (s : gset Z) : Z :=
    match elements s with
    | [] => 0
    | x :: xs => set_fold Z.min x s
    end.

Notation gset_interval := (fun (i j : Z) => (list_to_set (seqZ i j) : gset Z)).

Definition array_exchange {A : Type} (a1 a2 : list A) (i j : Z) : Prop :=
    match a2 !! Z.to_nat i, a2 !! Z.to_nat j with
    | Some vi, Some vj => a1 = <[Z.to_nat i := vj]>(<[Z.to_nat j := vi]>a2)
    | _, _ => False
    end.

From Stdlib Require Import Sorting.Permutation.

Definition permut_sub {A : Type} (a1 a2 : list A) (l u : nat) : Prop :=
  length a1 = length a2 ∧ (0 ≤ l ∧ l ≤ length a1)%nat ∧ (0 ≤ u ∧ u ≤ length a1)%nat ∧
  Permutation (slice a1 l u) (slice a2 l u).

Definition permut_sub' {A : Type} (a1 a2 : list A) (l u : nat) : Prop :=
  length a1 = length a2 ∧
  slice a1 0 l = slice a2 0 l ∧
  slice a1 u (length a1) = slice a2 u (length a1) ∧
  Permutation (slice a1 l u) (slice a2 l u).

Definition list_sum l := fold_right Z.add 0 l.

Notation count_occ' := (count_occ (fun x y => decide (x = y))).

Notation foldr' := (fun f l x => foldr f x l).
Notation list_to_gset := (fun l => list_to_set l : gset _).

Definition list_mem' {A} (eq : A -> A -> bool) (x : A) (l : list A) := forallb (eq x) l.

Definition Ztrunc (x : R) : Z := if Rle_dec 0 x then Zfloor x else Zceil x.
