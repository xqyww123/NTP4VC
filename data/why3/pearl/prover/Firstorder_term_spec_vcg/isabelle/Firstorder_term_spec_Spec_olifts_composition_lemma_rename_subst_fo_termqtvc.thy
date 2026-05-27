theory Firstorder_term_spec_Spec_olifts_composition_lemma_rename_subst_fo_termqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec"
begin
datatype ('b0, 'b3) fo_term_list = FONil | FOCons "('b0, 'b3) fo_term" "('b0, 'b3) fo_term_list"
     and ('b0, 'b3) fo_term = Var_fo_term "'b3" | App "'b0 symbol" "('b0, 'b3) fo_term_list"
fun nat_size_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> Nat_Nat.nat"  and nat_size_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> Nat_Nat.nat"  and size_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> int"  and size_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> int"
  where "nat_size_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) = (let s :: Nat_Nat.nat = SNat ONat in s)"
      | "nat_size_fo_term_list (FOCons v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_size_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_size_fo_term v0) s1 in s2)" for v0 v1
      | "nat_size_fo_term (Var_fo_term v0) = SNat ONat" for v0
      | "nat_size_fo_term (App v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_size_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_size_symbol v0) s1 in s2)" for v0 v1
      | "size_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) = (let s :: int = 1 :: int in s)"
      | "size_fo_term_list (FOCons v0 v1) = (let s :: int = 1 :: int; s1 :: int = size_fo_term_list v1 + s; s2 :: int = size_fo_term v0 + s1 in s2)" for v0 v1
      | "size_fo_term (Var_fo_term v0) = (1 :: int)" for v0
      | "size_fo_term (App v0 v1) = (let s :: int = 1 :: int; s1 :: int = size_fo_term_list v1 + s; s2 :: int = size_symbol v0 + s1 in s2)" for v0 v1
fun rename_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> ('b0 \<Rightarrow> 'c0) \<Rightarrow> ('b3 \<Rightarrow> 'c3) \<Rightarrow> ('c0, 'c3) fo_term_list"  and rename_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> ('b0 \<Rightarrow> 'c0) \<Rightarrow> ('b3 \<Rightarrow> 'c3) \<Rightarrow> ('c0, 'c3) fo_term"
  where "rename_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) s0 s3 = (FONil :: ('c0, 'c3) fo_term_list)" for s0 s3
      | "rename_fo_term_list (FOCons v0 v1) s0 s3 = FOCons (rename_fo_term v0 s0 s3) (rename_fo_term_list v1 s0 s3)" for v0 v1 s0 s3
      | "rename_fo_term (Var_fo_term v0) s0 s3 = Var_fo_term (s3 v0)" for v0 s0 s3
      | "rename_fo_term (App v0 v1) s0 s3 = App (rename_symbol v0 s0) (rename_fo_term_list v1 s0 s3)" for v0 v1 s0 s3
consts rename_subst_fo_term :: "('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0 \<Rightarrow> 'd0) \<Rightarrow> ('c3 \<Rightarrow> 'd3) \<Rightarrow> 'b3 \<Rightarrow> ('d0, 'd3) fo_term"
axiomatization where rename_subst_fo_term_definition:   "rename_subst_fo_term s0 s10 s13 x = rename_fo_term (s0 x) s10 s13"
  for s0 :: "'b3 \<Rightarrow> ('c0, 'c3) fo_term"
  and s10 :: "'c0 \<Rightarrow> 'd0"
  and s13 :: "'c3 \<Rightarrow> 'd3"
  and x :: "'b3"
definition olifts_fo_term :: "('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> 'b3 option \<Rightarrow> ('c0, 'c3 option) fo_term"
  where "olifts_fo_term s = ocase (rename_subst_fo_term s identity some) (Var_fo_term (None :: 'c3 option))" for s
theorem olifts_composition_lemma_rename_subst_fo_term'vc:
  fixes s23 :: "'c3 \<Rightarrow> ('d0, 'd3) fo_term"
  fixes s1 :: "'b3 \<Rightarrow> 'c3"
  shows "olifts_fo_term (compose s23 s1) = compose (olifts_fo_term s23) ((olift :: ('b3 \<Rightarrow> 'c3) \<Rightarrow> 'b3 option \<Rightarrow> 'c3 option) s1)"
  sorry
end
