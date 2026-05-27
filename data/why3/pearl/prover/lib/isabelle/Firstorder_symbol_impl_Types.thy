theory Firstorder_symbol_impl_Types
  imports "NTP4Verif.NTP4Verif" "Nat_Nat" "Functions_Config" "Functions_Func" "OptionFuncs_Funcs" "Sum_Sum" "Firstorder_symbol_spec_Spec"
begin
datatype 'b0 nl_symbol = NLFVar_symbol "'b0" | NLBruijn_symbol "int"
datatype  nlimpl_symbol = nlimpl_symbol'mk (nlrepr_symbol_field: "int nl_symbol") (nlfree_var_symbol_set_abstraction_symbol_field: "int") (model_symbol_field: "int symbol")
datatype  cons_symbol = NLCVar_symbol "int"
end
