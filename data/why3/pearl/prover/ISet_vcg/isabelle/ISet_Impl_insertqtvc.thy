theory ISet_Impl_insertqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.ISet_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.ISet_Logic"
begin
theorem insert'vc:
  fixes l :: "int list"
  fixes x :: "int"
  assumes fact0: "iset_ok l"
  shows "case l of Nil \<Rightarrow> True | Cons y q \<Rightarrow> \<not>x < y \<longrightarrow> y < x \<longrightarrow> (case l of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q) \<and> iset_ok q"
  and "\<forall>(result :: int list). (case l of Nil \<Rightarrow> result = Cons x (Nil :: int list) | Cons y q \<Rightarrow> (if x < y then result = Cons x l else if y < x then \<exists>(o1 :: int list). (iset_ok o1 \<and> (\<forall>(y1 :: int). y1 \<in> set o1 \<longleftrightarrow> y1 = x \<or> y1 \<in> set q)) \<and> result = Cons y o1 else result = l)) \<longrightarrow> iset_ok result \<and> (\<forall>(y :: int). y \<in> set result \<longleftrightarrow> y = x \<or> y \<in> set l)"
  sorry
end
