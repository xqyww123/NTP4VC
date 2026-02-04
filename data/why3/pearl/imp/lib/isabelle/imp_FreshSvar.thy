theory imp_FreshSvar
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/imp_Syntax" "../../lib/isabelle/imp_Svar" "../../lib/isabelle/imp_Constraint" "../../lib/isabelle/imp_SymState"
begin
definition is_fresh :: "svar \<Rightarrow> svar fset \<Rightarrow> _"
  where "is_fresh v vars \<longleftrightarrow> \<not>v |\<in>| vars" for v vars
end
