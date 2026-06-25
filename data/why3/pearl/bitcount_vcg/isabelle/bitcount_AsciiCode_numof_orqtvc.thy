theory bitcount_AsciiCode_numof_orqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or_def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
theorem numof_or'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes p :: "int \<Rightarrow> bool"
  fixes q :: "int \<Rightarrow> bool"
  assumes fact0: "\<forall>(i :: int). a \<le> i \<and> i < b \<longrightarrow> \<not>p i = True \<or> \<not>q i = True"
  shows "numof (fun_or p q) a b = numof p a b + numof q a b"
  sorry
end
