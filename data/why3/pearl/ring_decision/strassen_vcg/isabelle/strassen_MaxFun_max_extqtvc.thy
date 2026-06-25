theory strassen_MaxFun_max_extqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts maxf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where maxf_def:   "if b \<le> a then maxf f a b = (0 :: int) else maxf f a b = max (maxf f a (b - (1 :: int))) (f (b - (1 :: int)))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> int"
theorem max_ext'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> int"
  fixes g :: "int \<Rightarrow> int"
  assumes fact0: "a < b"
  assumes fact1: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> f i = g i"
  shows "maxf f a b = maxf g a b"
  sorry
end
