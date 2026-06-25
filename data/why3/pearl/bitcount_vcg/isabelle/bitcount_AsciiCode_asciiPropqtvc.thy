theory bitcount_AsciiCode_asciiPropqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "./bitcount_Hamming" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or_def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
theorem asciiProp'vc:
  fixes a :: "32 word"
  fixes b :: "32 word"
  shows "validAscii a \<and> \<not>validAscii b \<or> validAscii b \<and> \<not>validAscii a \<longleftrightarrow> odd (hammingD_logic a b)"
  sorry
end
