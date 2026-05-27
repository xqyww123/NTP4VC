theory imp_FreshSvar
  imports "NTP4Verif.NTP4Verif" "imp_Syntax" "imp_Svar" "imp_Constraint" "imp_SymState"
begin
definition is_fresh :: "svar \<Rightarrow> svar fset \<Rightarrow> _"
  where "is_fresh v vars \<longleftrightarrow> \<not>v |\<in>| vars" for v vars
end
