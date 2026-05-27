theory wp2_WP_assigns_reflqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp"
begin
typedecl  set
consts to_fset :: "set \<Rightarrow> int fset"
consts mk :: "int fset \<Rightarrow> set"
axiomatization where mk'spec:   "to_fset (mk s) = s"
  for s :: "int fset"
consts choose1 :: "set \<Rightarrow> int"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
definition assigns :: "(int \<Rightarrow> value) \<Rightarrow> int fset \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> _"
  where "assigns sigma a sigma' \<longleftrightarrow> (\<forall>(i :: int). \<not>i |\<in>| a \<longrightarrow> sigma i = sigma' i)" for sigma a sigma'
theorem assigns_refl'vc:
  fixes sigma :: "int \<Rightarrow> value"
  fixes a :: "int fset"
  shows "assigns sigma a sigma"
  sorry
end
