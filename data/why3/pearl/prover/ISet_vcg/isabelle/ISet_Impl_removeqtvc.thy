theory ISet_Impl_removeqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.ISet_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.ISet_Logic"
begin
theorem remove'vc:
  fixes l :: "int list"
  fixes x :: "int"
  assumes fact0: "iset_ok l"
  shows "case l of Nil \<Rightarrow> True | Cons y q \<Rightarrow> (case l of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q) \<and> iset_ok q"
  and "\<forall>(result :: int list). (case l of Nil \<Rightarrow> result = (Nil :: int list) | Cons y q \<Rightarrow> (if y = x then iset_ok result \<and> (\<forall>(y1 :: int). y1 \<in> set result \<longleftrightarrow> y1 \<in> set q \<and> \<not>y1 = x) else \<exists>(o1 :: int list). (iset_ok o1 \<and> (\<forall>(y1 :: int). y1 \<in> set o1 \<longleftrightarrow> y1 \<in> set q \<and> \<not>y1 = x)) \<and> result = Cons y o1)) \<longrightarrow> iset_ok result \<and> (\<forall>(y :: int). y \<in> set result \<longleftrightarrow> y \<in> set l \<and> \<not>y = x)"
  sorry
end
