theory Firstorder_symbol_spec_Spec_olifts_identity_symbolqtvc
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
definition olifts_symbol :: "('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> 'b0 option \<Rightarrow> 'c0 option symbol"
  where "olifts_symbol s = ocase (rename_subst_symbol s some) (Var_symbol (None :: 'c0 option))" for s
definition subst_symbol :: "'b0 symbol \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> 'c0 symbol"
  where "subst_symbol t s0 = (case t of Var_symbol v0 \<Rightarrow> s0 v0)" for t s0
consts subst_compose_symbol :: "('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> ('c0 \<Rightarrow> 'd0 symbol) \<Rightarrow> 'b0 \<Rightarrow> 'd0 symbol"
axiomatization where subst_compose_symbol_definition:   "subst_compose_symbol s0 s10 x = subst_symbol (s0 x) s10"
  for s0 :: "'b0 \<Rightarrow> 'c0 symbol"
  and s10 :: "'c0 \<Rightarrow> 'd0 symbol"
  and x :: "'b0"
consts subst_id_symbol :: "'b0 \<Rightarrow> 'b0 symbol"
axiomatization where subst_id_symbol_definition:   "subst_id_symbol x = Var_symbol x"
  for x :: "'b0"
theorem olifts_identity_symbol'vc:
  shows "(olifts_symbol :: ('b0 \<Rightarrow> 'b0 symbol) \<Rightarrow> 'b0 option \<Rightarrow> 'b0 option symbol) subst_id_symbol = subst_id_symbol"
  sorry
end
