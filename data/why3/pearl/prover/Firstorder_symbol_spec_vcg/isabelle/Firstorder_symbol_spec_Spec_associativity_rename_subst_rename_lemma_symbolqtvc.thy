theory Firstorder_symbol_spec_Spec_associativity_rename_subst_rename_lemma_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum"
begin
datatype 'b0 symbol = Var_symbol "'b0"
fun nat_size_symbol :: "'b0 symbol \<Rightarrow> Nat_Nat.nat"  and size_symbol :: "'b0 symbol \<Rightarrow> int"
  where "nat_size_symbol (Var_symbol v0) = SNat ONat" for v0
      | "size_symbol (Var_symbol v0) = (1 :: int)" for v0
definition rename_symbol :: "'b0 symbol \<Rightarrow> ('b0 \<Rightarrow> 'c0) \<Rightarrow> 'c0 symbol"
  where "rename_symbol t s0 = (case t of Var_symbol v0 \<Rightarrow> Var_symbol (s0 v0))" for t s0
consts rename_subst_symbol :: "('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> ('c0 \<Rightarrow> 'd0) \<Rightarrow> 'b0 \<Rightarrow> 'd0 symbol"
axiomatization where rename_subst_symbol_definition:   "rename_subst_symbol s0 s10 x = rename_symbol (s0 x) s10"
  for s0 :: "'b0 \<Rightarrow> 'c0 symbol"
  and s10 :: "'c0 \<Rightarrow> 'd0"
  and x :: "'b0"
theorem associativity_rename_subst_rename_lemma_symbol'vc:
  fixes s20 :: "'c0 \<Rightarrow> 'd0 symbol"
  fixes s30 :: "'d0 \<Rightarrow> 'e0"
  fixes s1 :: "'b0 \<Rightarrow> 'c0"
  shows "compose (rename_subst_symbol s20 s30) s1 = rename_subst_symbol (compose s20 s1) s30"
  sorry
end
