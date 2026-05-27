theory wp2_WP_assigns_transqtvc
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
theorem assigns_trans'vc:
  fixes sigma1 :: "int \<Rightarrow> value"
  fixes a :: "int fset"
  fixes sigma2 :: "int \<Rightarrow> value"
  fixes sigma3 :: "int \<Rightarrow> value"
  assumes fact0: "assigns sigma1 a sigma2"
  assumes fact1: "assigns sigma2 a sigma3"
  shows "assigns sigma1 a sigma3"
  sorry
end
