theory Predicates_Pred_pupdate_neqqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func"
begin
definition predExtensionalEqual :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> _"
  where "predExtensionalEqual p q \<longleftrightarrow> (\<forall>(x :: 'a). p x = True \<longleftrightarrow> q x = True)" for p q
axiomatization where predicateExtensionality:   "p = q"
 if "predExtensionalEqual p q"
  for p :: "'a \<Rightarrow> bool"
  and q :: "'a \<Rightarrow> bool"
definition evalp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> _"
  where "evalp p x \<longleftrightarrow> p x = True" for p x
consts pupdate :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where pupdate_def:   "pupdate p x y z = True \<longleftrightarrow> (if x = z then y = True else p z = True)"
  for p :: "'a \<Rightarrow> bool"
  and x :: "'a"
  and y :: "bool"
  and z :: "'a"
theorem pupdate_neq'vc:
  fixes x :: "'a"
  fixes z :: "'a"
  fixes p :: "'a \<Rightarrow> bool"
  fixes y :: "bool"
  assumes fact0: "\<not>x = z"
  shows "pupdate p x y z = True \<longleftrightarrow> p z = True"
  sorry
end
