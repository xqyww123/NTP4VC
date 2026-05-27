theory Unification_Types
  imports "NTP4Verif.NTP4Verif" "Functions_Config" "Functions_Func" "BacktrackArray_Types" "Predicates_Pred" "BacktrackArray_Logic" "Choice_Choice" "BacktrackArray_Impl" "Firstorder_symbol_spec_Spec" "Nat_Nat" "OptionFuncs_Funcs" "Sum_Sum" "Firstorder_symbol_impl_Types" "Firstorder_symbol_impl_Logic" "Firstorder_symbol_impl_Impl" "Firstorder_term_spec_Spec" "Firstorder_term_impl_Types" "Firstorder_term_impl_Logic" "Firstorder_term_impl_Impl"
begin
datatype  sdata = PConflict "nlimpl_fo_term_list" "nlimpl_fo_term_list" | Assign "nlimpl_fo_term"
typedecl  subst
typedecl  timesubst
datatype  unifier_subst = unifier_subst'mk (unifier_base_model: "int \<Rightarrow> (int, int) fo_term") (unifier: "int \<Rightarrow> (int, int) fo_term")
datatype  unification_return = unification_return'mk (final_unifier: "unifier_subst") (unifier_factor: "int \<Rightarrow> (int, int) fo_term")
end
