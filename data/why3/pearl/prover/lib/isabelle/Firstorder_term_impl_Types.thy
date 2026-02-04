theory Firstorder_term_impl_Types
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Nat_Nat" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func" "../../lib/isabelle/OptionFuncs_Funcs" "../../lib/isabelle/Sum_Sum" "../../lib/isabelle/Firstorder_symbol_spec_Spec" "../../lib/isabelle/Firstorder_symbol_impl_Types" "../../lib/isabelle/Firstorder_symbol_impl_Logic" "../../lib/isabelle/Firstorder_symbol_impl_Impl" "../../lib/isabelle/Firstorder_term_spec_Spec"
begin
datatype ('b0, 'b3) nl_fo_term_list = NL_FONil | NL_FOCons "('b0, 'b3) nl_fo_term" "('b0, 'b3) nl_fo_term_list"
     and ('b0, 'b3) nl_fo_term = NLFVar_fo_term "'b3" | NLBruijn_fo_term "int" | NL_App "'b0 nl_symbol" "('b0, 'b3) nl_fo_term_list"
datatype  nlimpl_fo_term_list = nlimpl_fo_term_list'mk (nlrepr_fo_term_list_field: "(int, int) nl_fo_term_list") (nlfree_var_symbol_set_abstraction_fo_term_list_field: "int") (nlfree_var_fo_term_set_abstraction_fo_term_list_field: "int") (model_fo_term_list_field: "(int, int) fo_term_list")
datatype  nlimpl_fo_term = nlimpl_fo_term'mk (nlrepr_fo_term_field: "(int, int) nl_fo_term") (nlfree_var_symbol_set_abstraction_fo_term_field: "int") (nlfree_var_fo_term_set_abstraction_fo_term_field: "int") (model_fo_term_field: "(int, int) fo_term")
datatype  cons_fo_term_list = NLC_FONil | NLC_FOCons "nlimpl_fo_term" "nlimpl_fo_term_list"
datatype  cons_fo_term = NLCVar_fo_term "int" | NLC_App "nlimpl_symbol" "nlimpl_fo_term_list"
end
