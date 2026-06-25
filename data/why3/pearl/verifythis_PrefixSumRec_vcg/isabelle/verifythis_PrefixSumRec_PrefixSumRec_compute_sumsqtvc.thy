theory verifythis_PrefixSumRec_PrefixSumRec_compute_sumsqtvc
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
definition partial_sum :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> _"
  where "partial_sum left1 right1 a0 a \<longleftrightarrow> (\<forall>(i :: int). left1 - (right1 - left1) < i \<and> i \<le> right1 \<longrightarrow> a ! nat i = sum_list (drop (0 :: nat) (take (nat i - (0 :: nat)) a0)))" for left1 right1 a0 a
theorem compute_sums'vc:
  fixes a :: "int list"
  fixes a0 :: "int list"
  assumes fact0: "(2 :: int) \<le> int (length a)"
  assumes fact1: "is_power_of_2 (int (length a))"
  assumes fact2: "length a0 = length a"
  assumes fact3: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a0) \<longrightarrow> a0 ! nat i = a ! nat i"
  shows "let l :: int = int (length a) in \<not>(2 :: int) = (0 :: int) \<and> (let left1 :: int = l cdiv (2 :: int) - (1 :: int); right1 :: int = l - (1 :: int) in (((0 :: int) \<le> left1 \<and> left1 < right1 \<and> right1 < int (length a)) \<and> -(1 :: int) \<le> left1 - (right1 - left1) \<and> is_power_of_2 (right1 - left1)) \<and> (\<forall>(a1 :: int list). length a1 = length a \<longrightarrow> phase1 left1 right1 a a1 \<and> (let space :: int = right1 - left1 in a1 ! nat right1 = sum_list (take (nat (right1 + (1 :: int)) - nat (left1 - space + (1 :: int))) (drop (nat (left1 - space + (1 :: int))) a)) \<and> (\<forall>(i :: int). i \<le> left1 - space \<longrightarrow> a1 ! nat i = a ! nat i) \<and> (\<forall>(i :: int). right1 < i \<longrightarrow> a1 ! nat i = a ! nat i)) \<longrightarrow> ((0 :: int) \<le> right1 \<and> right1 < int (length a1)) \<and> (length (a1[nat right1 := 0 :: int]) = length a1 \<longrightarrow> nth (a1[nat right1 := 0 :: int]) o nat = (nth a1 o nat)(right1 := 0 :: int) \<longrightarrow> (((0 :: int) \<le> left1 \<and> left1 < right1 \<and> right1 < int (length (a1[nat right1 := 0 :: int]))) \<and> -(1 :: int) \<le> left1 - (right1 - left1) \<and> is_power_of_2 (right1 - left1) \<and> a1[nat right1 := 0 :: int] ! nat right1 = sum_list (drop (0 :: nat) (take (nat (left1 - (right1 - left1) + (1 :: int)) - (0 :: nat)) a0)) \<and> phase1 left1 right1 a0 (a1[nat right1 := 0 :: int])) \<and> (\<forall>(a2 :: int list). length a2 = length (a1[nat right1 := 0 :: int]) \<longrightarrow> partial_sum left1 right1 a0 a2 \<and> (\<forall>(i :: int). i \<le> left1 - (right1 - left1) \<longrightarrow> a2 ! nat i = a1[nat right1 := 0 :: int] ! nat i) \<and> (\<forall>(i :: int). right1 < i \<longrightarrow> a2 ! nat i = a1[nat right1 := 0 :: int] ! nat i) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length a2) \<longrightarrow> a2 ! nat i = sum_list (drop (0 :: nat) (take (nat i - (0 :: nat)) a)))))))"
  sorry
end
