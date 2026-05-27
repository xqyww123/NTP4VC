theory ISet_Logic_iset_ok_charqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.ISet_Types" "pearl_prover_lib.Functions_Config"
begin
inductive iset_ok :: "int list \<Rightarrow> bool" where
   Set_empty: "iset_ok (Nil :: int list)"
 | Set_one: "iset_ok (Cons x (Nil :: int list))" for x :: "int"
 | Set_two: "iset_ok (Cons y q) \<Longrightarrow> x < y \<Longrightarrow> iset_ok (Cons x (Cons y q))" for y :: "int" and q :: "int list" and x :: "int"
theorem iset_ok_char'vc:
  fixes x :: "int"
  fixes l :: "int list"
  shows "iset_ok (Cons x l) \<longleftrightarrow> iset_ok l \<and> (\<forall>(y :: int). y \<in> set l \<longrightarrow> x < y)"
  sorry
end
