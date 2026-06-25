theory verifythis_PrefixSumRec_PrefixSumRec_phase1_frameqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum"
begin
definition is_power_of_2 :: "int \<Rightarrow> _"
  where "is_power_of_2 x \<longleftrightarrow> (\<exists>(k :: int). (0 :: int) \<le> k \<and> x = (2 :: int) ^\<^sub>i k)" for x
definition go_left :: "int \<Rightarrow> int \<Rightarrow> int"
  where "go_left left1 right1 = (let space :: int = right1 - left1 in left1 - space cdiv (2 :: int))" for left1 right1
definition go_right :: "int \<Rightarrow> int \<Rightarrow> int"
  where "go_right left1 right1 = (let space :: int = right1 - left1 in right1 - space cdiv (2 :: int))" for left1 right1
inductive phase1 :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
   Leaf: "right1 = left1 + (1 :: int) \<Longrightarrow> a ! nat left1 = a0 ! nat left1 \<Longrightarrow> phase1 left1 right1 a0 a" for right1 :: "int" and left1 :: "int" and a :: "int list" and a0 :: "int list"
 | Node: "left1 + (1 :: int) < right1 \<Longrightarrow> phase1 (go_left left1 right1) left1 a0 a \<Longrightarrow> phase1 (go_right left1 right1) right1 a0 a \<Longrightarrow> a ! nat left1 = sum_list (take (nat (left1 + (1 :: int)) - nat (left1 - (right1 - left1) + (1 :: int))) (drop (nat (left1 - (right1 - left1) + (1 :: int))) a0)) \<Longrightarrow> phase1 left1 right1 a0 a" for left1 :: "int" and right1 :: "int" and a0 :: "int list" and a :: "int list"
theorem phase1_frame'vc:
  fixes left1 :: "int"
  fixes right1 :: "int"
  fixes a :: "int list"
  fixes a' :: "int list"
  fixes a0 :: "int list"
  assumes fact0: "\<forall>(i :: int). left1 - (right1 - left1) < i \<and> i < right1 \<longrightarrow> a ! nat i = a' ! nat i"
  assumes fact1: "phase1 left1 right1 a0 a"
  shows "phase1 left1 right1 a0 a'"
  sorry
end
