theory sum_extended_Sum_extended_sum_addqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum"
begin
consts addf :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"
axiomatization where addf_def:   "addf f g x = f x + g x"
  for f :: "int \<Rightarrow> int"
  and g :: "int \<Rightarrow> int"
  and x :: "int"
consts smulf :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where smulf_def:   "smulf f l x = l * f x"
  for f :: "int \<Rightarrow> int"
  and l :: "int"
  and x :: "int"
theorem sum_add'vc:
  fixes f :: "int \<Rightarrow> int"
  fixes g :: "int \<Rightarrow> int"
  fixes a :: "int"
  fixes b :: "int"
  shows "sum (addf f g) a b = sum f a b + sum g a b"
  sorry
end
