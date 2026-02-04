theory sum_real_Sum
  imports "NTP4Verif.NTP4Verif"
begin
consts sum :: "(int \<Rightarrow> real) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real"
axiomatization where sum'def:   "if b \<le> a then sum f a b = (0 :: Real.real) else sum f a b = sum f a (b - (1 :: int)) + f (b - (1 :: int))"
  for b :: "int"
  and a :: "int"
  and f :: "int \<Rightarrow> real"
consts abs_fun :: "(int \<Rightarrow> real) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_fun'def:   "abs_fun f i = abs (f i)"
  for f :: "int \<Rightarrow> real"
  and i :: "int"
end
