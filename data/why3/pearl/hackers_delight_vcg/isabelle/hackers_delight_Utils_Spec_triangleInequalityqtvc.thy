theory hackers_delight_Utils_Spec_triangleInequalityqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition nth_diff :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> _"
  where "nth_diff a b i \<longleftrightarrow> \<not>((0 \<le> i \<and> bit a (nat i))) = ((0 \<le> i \<and> bit b (nat i)))" for a b i
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or_def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
theorem triangleInequality'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  fixes c :: "32 word"
  shows "hammingD a b + hammingD b c \<ge> hammingD a c"
  sorry
end
