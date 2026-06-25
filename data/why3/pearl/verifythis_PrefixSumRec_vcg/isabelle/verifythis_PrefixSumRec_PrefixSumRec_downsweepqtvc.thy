theory verifythis_PrefixSumRec_PrefixSumRec_downsweepqtvc
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
theorem downsweep'vc:
  fixes left1 :: "int"
  fixes right1 :: "int"
  fixes a :: "int list"
  fixes a0 :: "int list"
  assumes fact0: "(0 :: int) \<le> left1"
  assumes fact1: "left1 < right1"
  assumes fact2: "right1 < int (length a)"
  assumes fact3: "-(1 :: int) \<le> left1 - (right1 - left1)"
  assumes fact4: "is_power_of_2 (right1 - left1)"
  assumes fact5: "a ! nat right1 = sum_list (drop (0 :: nat) (take (nat (left1 - (right1 - left1) + (1 :: int)) - (0 :: nat)) a0))"
  assumes fact6: "phase1 left1 right1 a0 a"
  shows "(0 :: int) \<le> right1"
  and "right1 < int (length a)"
  and "let tmp :: int = a ! nat right1 in ((0 :: int) \<le> left1 \<and> left1 < int (length a)) \<and> ((0 :: int) \<le> right1 \<and> right1 < int (length a)) \<and> (let o1 :: int = a ! nat right1 + a ! nat left1 in ((0 :: int) \<le> right1 \<and> right1 < int (length a)) \<and> (length (a[nat right1 := o1]) = length a \<longrightarrow> nth (a[nat right1 := o1]) o nat = (nth a o nat)(right1 := o1) \<longrightarrow> ((0 :: int) \<le> left1 \<and> left1 < int (length (a[nat right1 := o1]))) \<and> (length (a[nat left1 := tmp, nat right1 := o1]) = length (a[nat right1 := o1]) \<longrightarrow> nth (a[nat left1 := tmp, nat right1 := o1]) o nat = (nth (a[nat right1 := o1]) o nat)(left1 := tmp) \<longrightarrow> (if left1 + (1 :: int) < right1 then let space :: int = right1 - left1 in \<not>(2 :: int) = (0 :: int) \<and> (let o2 :: int = left1 - space cdiv (2 :: int) in (((0 :: int) \<le> right1 - left1 \<and> left1 - o2 < right1 - left1) \<and> ((0 :: int) \<le> o2 \<and> o2 < left1 \<and> left1 < int (length (a[nat left1 := tmp, nat right1 := o1]))) \<and> -(1 :: int) \<le> o2 - (left1 - o2) \<and> is_power_of_2 (left1 - o2) \<and> a[nat left1 := tmp, nat right1 := o1] ! nat left1 = sum_list (drop (0 :: nat) (take (nat (o2 - (left1 - o2) + (1 :: int)) - (0 :: nat)) a0)) \<and> phase1 o2 left1 a0 (a[nat left1 := tmp, nat right1 := o1])) \<and> (\<forall>(a1 :: int list). length a1 = length (a[nat left1 := tmp, nat right1 := o1]) \<longrightarrow> partial_sum o2 left1 a0 a1 \<and> (\<forall>(i :: int). i \<le> o2 - (left1 - o2) \<longrightarrow> a1 ! nat i = a[nat left1 := tmp, nat right1 := o1] ! nat i) \<and> (\<forall>(i :: int). left1 < i \<longrightarrow> a1 ! nat i = a[nat left1 := tmp, nat right1 := o1] ! nat i) \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> (let o3 :: int = right1 - space cdiv (2 :: int) in (((0 :: int) \<le> right1 - left1 \<and> right1 - o3 < right1 - left1) \<and> ((0 :: int) \<le> o3 \<and> o3 < right1 \<and> right1 < int (length a1)) \<and> -(1 :: int) \<le> o3 - (right1 - o3) \<and> is_power_of_2 (right1 - o3) \<and> a1 ! nat right1 = sum_list (drop (0 :: nat) (take (nat (o3 - (right1 - o3) + (1 :: int)) - (0 :: nat)) a0)) \<and> phase1 o3 right1 a0 a1) \<and> (\<forall>(a2 :: int list). length a2 = length a1 \<longrightarrow> partial_sum o3 right1 a0 a2 \<and> (\<forall>(i :: int). i \<le> o3 - (right1 - o3) \<longrightarrow> a2 ! nat i = a1 ! nat i) \<and> (\<forall>(i :: int). right1 < i \<longrightarrow> a2 ! nat i = a1 ! nat i) \<longrightarrow> partial_sum left1 right1 a0 a2 \<and> (\<forall>(i :: int). i \<le> left1 - (right1 - left1) \<longrightarrow> a2 ! nat i = a ! nat i) \<and> (\<forall>(i :: int). right1 < i \<longrightarrow> a2 ! nat i = a ! nat i))))) else partial_sum left1 right1 a0 (a[nat left1 := tmp, nat right1 := o1]) \<and> (\<forall>(i :: int). i \<le> left1 - (right1 - left1) \<longrightarrow> a[nat left1 := tmp, nat right1 := o1] ! nat i = a ! nat i) \<and> (\<forall>(i :: int). right1 < i \<longrightarrow> a[nat left1 := tmp, nat right1 := o1] ! nat i = a ! nat i)))))"
  sorry
end
