theory imp_SymStateSet
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/imp_Syntax" "../../lib/isabelle/imp_Svar" "../../lib/isabelle/imp_Constraint" "../../lib/isabelle/imp_SymState"
begin
typedecl  set
consts to_fset :: "set \<Rightarrow> sym_state fset"
consts mk :: "sym_state fset \<Rightarrow> set"
axiomatization where mk'spec:   "to_fset (mk s) = s"
  for s :: "sym_state fset"
consts choose1 :: "set \<Rightarrow> sym_state"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
consts to_list :: "set \<Rightarrow> sym_state list"
axiomatization where to_list'spec:   "e |\<in>| to_fset s \<longleftrightarrow> e \<in> List.set (to_list s)"
  for e :: "sym_state"
  and s :: "set"
consts of_list :: "sym_state list \<Rightarrow> set"
axiomatization where of_list'spec:   "e |\<in>| to_fset (of_list l) \<longleftrightarrow> e \<in> List.set l"
  for e :: "sym_state"
  and l :: "sym_state list"
end
