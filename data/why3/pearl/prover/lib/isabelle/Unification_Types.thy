theory Unification_Types
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func" "../../lib/isabelle/BacktrackArray_Types" "../../lib/isabelle/Predicates_Pred" "../../lib/isabelle/BacktrackArray_Logic" "../../lib/isabelle/Choice_Choice" "../../lib/isabelle/BacktrackArray_Impl" "../../lib/isabelle/Firstorder_symbol_spec_Spec" "../../lib/isabelle/Nat_Nat" "../../lib/isabelle/OptionFuncs_Funcs" "../../lib/isabelle/Sum_Sum" "../../lib/isabelle/Firstorder_symbol_impl_Types" "../../lib/isabelle/Firstorder_symbol_impl_Logic" "../../lib/isabelle/Firstorder_symbol_impl_Impl" "../../lib/isabelle/Firstorder_term_spec_Spec" "../../lib/isabelle/Firstorder_term_impl_Types" "../../lib/isabelle/Firstorder_term_impl_Logic" "../../lib/isabelle/Firstorder_term_impl_Impl"
begin
datatype  sdata = PConflict "nlimpl_fo_term_list" "nlimpl_fo_term_list" | Assign "nlimpl_fo_term"
typedecl  subst
typedecl  timesubst
datatype  unifier_subst = unifier_subst'mk (unifier_base_model: "int \<Rightarrow> (int, int) fo_term") (unifier: "int \<Rightarrow> (int, int) fo_term")
datatype  unification_return = unification_return'mk (final_unifier: "unifier_subst") (unifier_factor: "int \<Rightarrow> (int, int) fo_term")
end
