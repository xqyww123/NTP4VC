theory bitcount_AsciiCode_tmp_lemmaqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "./bitcount_Hamming" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or_def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
consts nth_closure :: "32 word \<Rightarrow> int \<Rightarrow> bool"
consts nth_diff_closure :: "32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> bool"
theorem tmp_lemma'vc:
  fixes i :: "int"
  fixes j :: "int"
  fixes a :: "32 word"
  fixes b :: "32 word"
  assumes fact0: "i < j"
  shows "even (numof (nth_closure a) i j) \<and> odd (numof (nth_closure b) i j) \<or> odd (numof (nth_closure a) i j) \<and> even (numof (nth_closure b) i j) \<longleftrightarrow> odd (numof (nth_diff_closure a b) i j)"
  sorry
end
