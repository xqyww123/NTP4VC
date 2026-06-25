theory sum_real_Sum_sum_boundsqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts sum :: "(int \<Rightarrow> real) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real"
axiomatization where sum_def:   "if b \<le> a then sum f a b = (0 :: Real.real) else sum f a b = sum f a (b - (1 :: int)) + f (b - (1 :: int))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> real"
consts abs_fun :: "(int \<Rightarrow> real) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_fun_def:   "abs_fun f i = abs (f i)"
  for f :: "int \<Rightarrow> real"
  and i :: "int"
theorem sum_bounds'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes min :: "real"
  fixes f :: "int \<Rightarrow> real"
  fixes max :: "real"
  assumes fact0: "a \<le> b"
  assumes fact1: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> min \<le> f i \<and> f i \<le> max"
  shows "real_of_int (b - a) * min \<le> sum f a b"
  and "sum f a b \<le> real_of_int (b - a) * max"
  sorry
end
