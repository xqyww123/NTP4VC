theory Predicates_Pred_pcompose_associativeqtvc
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
consts pcompose :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where pcompose_def:   "pcompose p f x = True \<longleftrightarrow> p (f x) = True"
  for p :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
theorem pcompose_associative'vc:
  fixes p :: "'c \<Rightarrow> bool"
  fixes g :: "'b \<Rightarrow> 'c"
  fixes f :: "'a \<Rightarrow> 'b"
  shows "pcompose (pcompose p g) f = pcompose p (compose g f)"
  sorry
end
