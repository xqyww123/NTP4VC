theory fibonacci_FibonacciTailRecList_sum_fib_accqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Fibonacci"
begin
consts sum_fib :: "int list \<Rightarrow> int"
axiomatization where sum_fib_def:   "case l of Nil \<Rightarrow> sum_fib l = (0 :: int) | Cons x r \<Rightarrow> sum_fib l = fib x + sum_fib r"
 if "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  for l :: "int list"
consts sum_pow :: "int list \<Rightarrow> int"
axiomatization where sum_pow_def:   "case l of Nil \<Rightarrow> sum_pow l = (0 :: int) | Cons x r \<Rightarrow> sum_pow l = (2 :: int) ^\<^sub>i x + sum_pow r"
 if "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  for l :: "int list"
axiomatization where sum_pow'spec:   "(0 :: int) \<le> sum_pow l"
 if "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  for l :: "int list"
theorem sum_fib_acc'vc:
  fixes l :: "int list"
  fixes acc :: "int"
  assumes fact0: "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  shows "case l of Nil \<Rightarrow> True | Cons n r \<Rightarrow> (if n \<le> (1 :: int) then ((0 :: int) \<le> sum_pow l \<and> sum_pow r < sum_pow l) \<and> (\<forall>(n1 :: int). n1 \<in> set r \<longrightarrow> (0 :: int) \<le> n1) else let l2 :: int list = Cons (n - (1 :: int)) (Cons (n - (2 :: int)) r) in ((0 :: int) \<le> sum_pow l \<and> sum_pow l2 < sum_pow l) \<and> (\<forall>(n1 :: int). n1 \<in> set l2 \<longrightarrow> (0 :: int) \<le> n1))"
  and "\<forall>(result :: int). (case l of Nil \<Rightarrow> result = acc | Cons n r \<Rightarrow> (if n \<le> (1 :: int) then result = acc + n + sum_fib r else result = acc + sum_fib (Cons (n - (1 :: int)) (Cons (n - (2 :: int)) r)))) \<longrightarrow> result = acc + sum_fib l"
  sorry
end
