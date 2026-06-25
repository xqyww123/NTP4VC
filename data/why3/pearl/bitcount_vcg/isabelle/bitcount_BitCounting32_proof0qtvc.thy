theory bitcount_BitCounting32_proof0qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
definition step0 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step0 n x1 \<longleftrightarrow> x1 = n - ((n >> unat (1 :: 32 word)) AND (1431655765 :: 32 word))" for n x1
consts nth_closure :: "32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_closure_def:   "nth_closure y y1 = ((0 \<le> y1 \<and> bit y (nat y1)))"
  for y :: "32 word"
  and y1 :: "int"
theorem proof0'vc:
  fixes i :: "int"
  fixes n :: "32 word"
  fixes x1 :: "32 word"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (16 :: int)"
  assumes fact2: "step0 n x1"
  shows "uint ((x1 >> nat ((2 :: int) * i)) AND (3 :: 32 word)) = numof (nth_closure n) ((2 :: int) * i) ((2 :: int) * i + (2 :: int))"
  sorry
end
