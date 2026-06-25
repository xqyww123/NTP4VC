theory strassen_MaxFun_max_leftqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts maxf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where maxf_def:   "if b \<le> a then maxf f a b = (0 :: int) else maxf f a b = max (maxf f a (b - (1 :: int))) (f (b - (1 :: int)))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> int"
theorem max_left'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> int"
  assumes fact0: "a < b"
  shows "maxf f a b = max (f a) (maxf f (a + (1 :: int)) b)"
  sorry
end
