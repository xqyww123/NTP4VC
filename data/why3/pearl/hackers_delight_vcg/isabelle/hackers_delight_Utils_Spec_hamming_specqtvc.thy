theory hackers_delight_Utils_Spec_hamming_specqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.int_NumOf" "./hackers_delight_Utils"
begin
definition nth_diff :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> _"
  where "nth_diff a b i \<longleftrightarrow> \<not>((0 \<le> i \<and> bit a (nat i))) = ((0 \<le> i \<and> bit b (nat i)))" for a b i
consts nth_diff_closure :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_diff_closure_def:   "nth_diff_closure y y1 y2 = True \<longleftrightarrow> nth_diff y y1 y2"
  for y :: "32 word"
  and y1 :: "32 word"
  and y2 :: "int"
theorem hamming_spec'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  shows "uint (hammingD a b) = numof (nth_diff_closure a b) (0 :: int) (32 :: int)"
  sorry
end
