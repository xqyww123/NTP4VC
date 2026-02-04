theory Predicates_Pred
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func"
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
consts pcompose :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where pcompose_def:   "pcompose p f x = True \<longleftrightarrow> p (f x) = True"
  for p :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
consts pfalse :: "'a \<Rightarrow> bool"
axiomatization where pfalse_def:   "\<not>pfalse x = True"
  for x :: "'a"
consts ptrue :: "'a \<Rightarrow> bool"
axiomatization where ptrue_def:   "ptrue x = True"
  for x :: "'a"
end
