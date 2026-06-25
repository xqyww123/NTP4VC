theory strassen_MaxFun_maxf_nonnegqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts maxf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where maxf_def:   "if b \<le> a then maxf f a b = (0 :: int) else maxf f a b = max (maxf f a (b - (1 :: int))) (f (b - (1 :: int)))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> int"
theorem maxf_nonneg'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> int"
  assumes fact0: "a \<le> b"
  shows "(0 :: int) \<le> maxf f a b"
  sorry
end
