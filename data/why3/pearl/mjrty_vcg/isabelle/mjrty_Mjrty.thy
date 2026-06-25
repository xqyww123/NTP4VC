theory mjrty_Mjrty
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
consts fc :: "'a list \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc_def:   "fc a v i = True \<longleftrightarrow> a ! nat i = v"
  for a :: "'a list"
  and v :: "'a"
  and i :: "int"
typedecl  candidate
end
