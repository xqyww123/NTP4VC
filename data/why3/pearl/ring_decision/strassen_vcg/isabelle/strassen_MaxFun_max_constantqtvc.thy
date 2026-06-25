theory strassen_MaxFun_max_constantqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts maxf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where maxf_def:   "if b \<le> a then maxf f a b = (0 :: int) else maxf f a b = max (maxf f a (b - (1 :: int))) (f (b - (1 :: int)))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> int"
theorem max_constant'vc:
  fixes v :: "int"
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> v"
  assumes fact1: "a < b"
  assumes fact2: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> f i = v"
  shows "maxf f a b = v"
  sorry
end
