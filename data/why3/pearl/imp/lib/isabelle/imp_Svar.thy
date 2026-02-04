theory imp_Svar
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  svar
consts eq :: "svar \<Rightarrow> svar \<Rightarrow> bool"
axiomatization where eq'spec:   "eq v1 v2 \<longleftrightarrow> v1 = v2"
  for v1 :: "svar"
  and v2 :: "svar"
typedecl  set
consts to_fset :: "set \<Rightarrow> svar fset"
consts mk :: "svar fset \<Rightarrow> set"
axiomatization where mk'spec:   "to_fset (mk s) = s"
  for s :: "svar fset"
consts choose1 :: "set \<Rightarrow> svar"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
end
