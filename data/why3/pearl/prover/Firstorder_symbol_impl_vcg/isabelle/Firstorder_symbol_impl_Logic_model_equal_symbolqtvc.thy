theory Firstorder_symbol_impl_Logic_model_equal_symbolqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec"
begin
fun nat_nlsize_symbol :: "'b0 nl_symbol \<Rightarrow> Nat_Nat.nat"  and nlsize_symbol :: "'b0 nl_symbol \<Rightarrow> int"
  where "nat_nlsize_symbol (NLFVar_symbol v0) = SNat ONat" for v0
      | "nat_nlsize_symbol (NLBruijn_symbol v0) = SNat ONat" for v0
      | "nlsize_symbol (NLFVar_symbol v0) = (1 :: int)" for v0
      | "nlsize_symbol (NLBruijn_symbol v0) = (1 :: int)" for v0
consts shiftb_symbol :: "(int \<Rightarrow> 'b0 symbol) \<Rightarrow> int \<Rightarrow> 'b0 option symbol"
axiomatization where shiftb_symbol_definition:   "shiftb_symbol bnd i = (if i = (0 :: int) then Var_symbol (None :: 'b0 option) else rename_symbol (bnd (i - (1 :: int))) some)"
  for bnd :: "int \<Rightarrow> 'b0 symbol"
  and i :: "int"
definition nlmodel_symbol :: "'b0 nl_symbol \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> (int \<Rightarrow> 'c0 symbol) \<Rightarrow> 'c0 symbol"
  where "nlmodel_symbol t fr0 bnd0 = (case t of NLFVar_symbol v0 \<Rightarrow> fr0 v0 | NLBruijn_symbol v0 \<Rightarrow> bnd0 v0)" for t fr0 bnd0
definition correct_indexes_symbol :: "'b0 nl_symbol \<Rightarrow> _"
  where "correct_indexes_symbol t \<longleftrightarrow> (case t of NLFVar_symbol v0 \<Rightarrow> True | NLBruijn_symbol v0 \<Rightarrow> (0 :: int) \<le> v0)" for t
definition bound_depth_of_symbol_in_symbol :: "'b0 nl_symbol \<Rightarrow> int"
  where "bound_depth_of_symbol_in_symbol t = (case t of NLFVar_symbol v0 \<Rightarrow> (0 :: int) | NLBruijn_symbol v0 \<Rightarrow> (1 :: int) + v0)" for t
theorem model_equal_symbol'vc:
  fixes t :: "'b0 nl_symbol"
  fixes bnd10 :: "int \<Rightarrow> 'c0 symbol"
  fixes bnd20 :: "int \<Rightarrow> 'c0 symbol"
  fixes fr10 :: "'b0 \<Rightarrow> 'c0 symbol"
  assumes fact0: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < bound_depth_of_symbol_in_symbol t \<longrightarrow> bnd10 i = bnd20 i"
  assumes fact1: "correct_indexes_symbol t"
  shows "nlmodel_symbol t fr10 bnd10 = nlmodel_symbol t fr10 bnd20"
  sorry
end
