theory fibonacci_FibonacciTailRecList_fibqtvc
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
theorem fib'vc:
  fixes n :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  shows "let o1 :: int list = Cons n (Nil :: int list) in (\<forall>(n1 :: int). n1 \<in> set o1 \<longrightarrow> (0 :: int) \<le> n1) \<and> (0 :: int) + sum_fib o1 = fib n"
  sorry
end
