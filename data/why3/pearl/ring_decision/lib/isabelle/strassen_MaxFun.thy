theory strassen_MaxFun
  imports "NTP4Verif.NTP4Verif"
begin
consts maxf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where maxf'def:   "if b \<le> a then maxf f a b = (0 :: int) else maxf f a b = max (maxf f a (b - (1 :: int))) (f (b - (1 :: int)))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> int"
end
