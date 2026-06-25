theory fibonacci_FibonacciTailRecList_sum_powqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Fibonacci"
begin
consts sum_fib :: "int list \<Rightarrow> int"
axiomatization where sum_fib_def:   "case l of Nil \<Rightarrow> sum_fib l = (0 :: int) | Cons x r \<Rightarrow> sum_fib l = fib x + sum_fib r"
 if "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  for l :: "int list"
theorem sum_pow'vc:
  fixes l :: "int list"
  assumes fact0: "\<forall>(n :: int). n \<in> set l \<longrightarrow> (0 :: int) \<le> n"
  shows "case l of Nil \<Rightarrow> True | Cons x r \<Rightarrow> (\<forall>(n :: int). n \<in> set r \<longrightarrow> (0 :: int) \<le> n)"
  and "\<forall>(result :: int). (case l of Nil \<Rightarrow> result = (0 :: int) | Cons x r \<Rightarrow> (\<exists>(o1 :: int). (0 :: int) \<le> o1 \<and> result = (2 :: int) ^\<^sub>i x + o1)) \<longrightarrow> (0 :: int) \<le> result"
  sorry
end
