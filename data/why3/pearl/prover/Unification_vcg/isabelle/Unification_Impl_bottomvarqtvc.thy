theory Unification_Impl_bottomvarqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_prover_lib.Unification_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice" "pearl_prover_lib.BacktrackArray_Impl" "pearl_prover_lib.Firstorder_symbol_spec_Spec" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_impl_Types" "pearl_prover_lib.Firstorder_symbol_impl_Logic" "pearl_prover_lib.Firstorder_symbol_impl_Impl" "pearl_prover_lib.Firstorder_term_spec_Spec" "pearl_prover_lib.Firstorder_term_impl_Types" "pearl_prover_lib.Firstorder_term_impl_Logic" "pearl_prover_lib.Firstorder_term_impl_Impl" "pearl_prover_lib.Unification_Logic"
begin
theorem bottomvar'vc:
  fixes rhob :: "sdata t"
  fixes rho :: "unifier_subst"
  fixes x :: "int"
  assumes fact0: "unifier_subst_ok rhob rho"
  assumes fact1: "unassigned (current_timestamp rhob) x"
  shows "let tm :: (int, int) fo_term = Var_fo_term x in tm = subst_fo_term tm subst_id_symbol (unifier_base_model rho) \<and> tm = subst_fo_term tm subst_id_symbol (unifier rho)"
  sorry
end
