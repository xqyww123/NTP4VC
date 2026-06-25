theory bitcount_Hamming_symmetricqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "mach.bv_BVCheck32"
begin
definition nth_diff :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> _"
  where "nth_diff a b i \<longleftrightarrow> \<not>((0 \<le> i \<and> bit a (nat i))) = ((0 \<le> i \<and> bit b (nat i)))" for a b i
consts nth_diff_closure :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_diff_closure_def:   "nth_diff_closure y y1 y2 = True \<longleftrightarrow> nth_diff y y1 y2"
  for y :: "32 word"
  and y1 :: "32 word"
  and y2 :: "int"
definition hammingD_logic :: "32 word \<Rightarrow> 32 word \<Rightarrow> int"
  where "hammingD_logic a b = numof (nth_diff_closure a b) (0 :: int) (32 :: int)" for a b
theorem symmetric'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  shows "hammingD_logic a b = hammingD_logic b a"
  sorry
end
