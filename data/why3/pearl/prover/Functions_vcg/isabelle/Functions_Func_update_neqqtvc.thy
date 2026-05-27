theory Functions_Func_update_neqqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Functions_Config"
begin
definition extensionalEqual :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> _"
  where "extensionalEqual f g \<longleftrightarrow> (\<forall>(x :: 'a). f x = g x)" for f g
axiomatization where functionExtensionality:   "f = g"
 if "extensionalEqual f g"
  for f :: "'a \<Rightarrow> 'b"
  and g :: "'a \<Rightarrow> 'b"
consts update :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
axiomatization where update_def:   "update f x y z = (if x = z then y else f z)"
  for f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
  and y :: "'b"
  and z :: "'a"
theorem update_neq'vc:
  fixes x :: "'a"
  fixes z :: "'a"
  fixes f :: "'a \<Rightarrow> 'b"
  fixes y :: "'b"
  assumes fact0: "\<not>x = z"
  shows "update f x y z = f z"
  sorry
end
