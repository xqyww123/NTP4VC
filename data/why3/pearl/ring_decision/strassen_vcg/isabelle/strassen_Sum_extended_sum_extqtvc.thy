theory strassen_Sum_extended_sum_extqtvc
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
consts sumf :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where sumf_def:   "sumf f a b x = sum (f x) a b"
  for f :: "int \<Rightarrow> int \<Rightarrow> int"
  and a :: "int"
  and b :: "int"
  and x :: "int"
theorem sum_ext'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes f :: "int \<Rightarrow> int"
  fixes g :: "int \<Rightarrow> int"
  assumes fact0: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> f i = g i"
  shows "sum f a b = sum g a b"
  sorry
end
