theory Firstorder_symbol_impl_Impl_unbind_var_symbol_in_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Firstorder_symbol_impl_Logic"
begin
theorem unbind_var_symbol_in_symbol'vc:
  fixes i :: "int"
  fixes t :: "int nl_symbol"
  fixes x :: "int nl_symbol"
  fixes fr0 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd10 :: "int \<Rightarrow> 'b0 symbol"
  fixes bnd20 :: "int \<Rightarrow> 'b0 symbol"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "correct_indexes_symbol t"
  assumes fact2: "bound_depth_of_symbol_in_symbol t \<le> i + (1 :: int)"
  assumes fact3: "correct_indexes_symbol x"
  assumes fact4: "bound_depth_of_symbol_in_symbol x = (0 :: int)"
  shows "case t of NLFVar_symbol v0 \<Rightarrow> True | NLBruijn_symbol v0 \<Rightarrow> True"
  and "\<forall>(result :: int nl_symbol). (case t of NLFVar_symbol v0 \<Rightarrow> result = NLFVar_symbol v0 | NLBruijn_symbol v0 \<Rightarrow> (if v0 = i then result = x else result = NLBruijn_symbol v0)) \<longrightarrow> correct_indexes_symbol result \<and> bound_depth_of_symbol_in_symbol result \<le> i \<and> nlmodel_symbol result fr0 bnd10 = nlmodel_symbol t fr0 (update bnd10 i (nlmodel_symbol x fr0 bnd20))"
  sorry
end
