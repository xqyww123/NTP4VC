theory hackers_delight_Utils_Spec_symmetricqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition nth_diff :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> _"
  where "nth_diff a b i \<longleftrightarrow> \<not>((0 \<le> i \<and> bit a (nat i))) = ((0 \<le> i \<and> bit b (nat i)))" for a b i
theorem symmetric'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  shows "hammingD a b = hammingD b a"
  sorry
end
