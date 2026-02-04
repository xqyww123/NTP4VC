theory Firstorder_symbol_impl_Logic
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Firstorder_symbol_impl_Types" "../../lib/isabelle/Nat_Nat" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func" "../../lib/isabelle/OptionFuncs_Funcs" "../../lib/isabelle/Sum_Sum" "../../lib/isabelle/Firstorder_symbol_spec_Spec"
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
definition nlimpl_symbol_ok :: "nlimpl_symbol \<Rightarrow> _"
  where "nlimpl_symbol_ok t \<longleftrightarrow> nlmodel_symbol (nlrepr_symbol_field t) subst_id_symbol ((const :: int symbol \<Rightarrow> int \<Rightarrow> int symbol) (Var_symbol (-(1 :: int)))) = model_symbol_field t \<and> correct_indexes_symbol (nlrepr_symbol_field t) \<and> bound_depth_of_symbol_in_symbol (nlrepr_symbol_field t) = (0 :: int) \<and> (\<forall>(x :: int). is_symbol_free_var_in_symbol x (model_symbol_field t) \<longrightarrow> x < nlfree_var_symbol_set_abstraction_symbol_field t)" for t
definition cons_ok_symbol :: "cons_symbol \<Rightarrow> _"
  where "cons_ok_symbol c \<longleftrightarrow> (case c of NLCVar_symbol v0 \<Rightarrow> True)" for c
definition cons_rel_symbol :: "cons_symbol \<Rightarrow> nlimpl_symbol \<Rightarrow> _"
  where "cons_rel_symbol c t \<longleftrightarrow> (case c of NLCVar_symbol v0 \<Rightarrow> model_symbol_field t = Var_symbol v0)" for c t
definition cons_open_rel_symbol :: "cons_symbol \<Rightarrow> nlimpl_symbol \<Rightarrow> _"
  where "cons_open_rel_symbol c t \<longleftrightarrow> (case c of NLCVar_symbol v0 \<Rightarrow> model_symbol_field t = Var_symbol v0)" for c t
end
