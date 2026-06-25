theory bitcount_AsciiCode_count_orqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or_def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
theorem count_or'vc:
  fixes b :: "32 word"
  fixes c :: "32 word"
  assumes fact0: "b AND c = (0 :: 32 word)"
  shows "count_logic (b OR c) = count_logic b + count_logic c"
  sorry
end
