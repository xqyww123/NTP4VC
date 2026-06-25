theory sum_real_Sum_sum_strictly_posqtvc
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
theorem sum_strictly_pos'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> real"
  assumes fact0: "a < b"
  assumes fact1: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> (0 :: Real.real) < f i"
  shows "(0 :: Real.real) < sum f a b"
  sorry
end
