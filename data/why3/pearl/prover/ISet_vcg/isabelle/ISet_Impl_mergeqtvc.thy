theory ISet_Impl_mergeqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.ISet_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.ISet_Logic"
begin
theorem merge'vc:
  fixes l1 :: "int list"
  fixes l2 :: "int list"
  assumes fact0: "iset_ok l1"
  assumes fact1: "iset_ok l2"
  shows "case l1 of Nil \<Rightarrow> True | Cons x q1 \<Rightarrow> (case l2 of Nil \<Rightarrow> True | Cons y q2 \<Rightarrow> (if x < y then (case l1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q1) \<and> iset_ok q1 \<and> iset_ok l2 else if y < x then (case l2 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q2) \<and> iset_ok l1 \<and> iset_ok q2 else ((case l1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q1) \<or> l1 = q1 \<and> (case l2 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = q2)) \<and> iset_ok q1 \<and> iset_ok q2))"
  and "\<forall>(result :: int list). (case l1 of Nil \<Rightarrow> result = l2 | Cons x q1 \<Rightarrow> (case l2 of Nil \<Rightarrow> result = l1 | Cons y q2 \<Rightarrow> (if x < y then \<exists>(o1 :: int list). (iset_ok o1 \<and> (\<forall>(y1 :: int). y1 \<in> set o1 \<longleftrightarrow> y1 \<in> set q1 \<or> y1 \<in> set l2)) \<and> result = Cons x o1 else if y < x then \<exists>(o1 :: int list). (iset_ok o1 \<and> (\<forall>(y1 :: int). y1 \<in> set o1 \<longleftrightarrow> y1 \<in> set l1 \<or> y1 \<in> set q2)) \<and> result = Cons y o1 else \<exists>(o1 :: int list). (iset_ok o1 \<and> (\<forall>(y1 :: int). y1 \<in> set o1 \<longleftrightarrow> y1 \<in> set q1 \<or> y1 \<in> set q2)) \<and> result = Cons x o1))) \<longrightarrow> iset_ok result \<and> (\<forall>(y :: int). y \<in> set result \<longleftrightarrow> y \<in> set l1 \<or> y \<in> set l2)"
  sorry
end
