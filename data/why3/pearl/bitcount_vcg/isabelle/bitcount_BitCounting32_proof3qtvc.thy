theory bitcount_BitCounting32_proof3qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
definition step0 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step0 n x1 \<longleftrightarrow> x1 = n - ((n >> unat (1 :: 32 word)) AND (1431655765 :: 32 word))" for n x1
definition step1 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step1 x1 x2 \<longleftrightarrow> x2 = (x1 AND (858993459 :: 32 word)) + ((x1 >> unat (2 :: 32 word)) AND (858993459 :: 32 word))" for x1 x2
definition step2 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step2 x2 x3 \<longleftrightarrow> x3 = x2 + (x2 >> unat (4 :: 32 word)) AND (252645135 :: 32 word)" for x2 x3
definition step3 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step3 x3 x4 \<longleftrightarrow> x4 = x3 + (x3 >> unat (8 :: 32 word))" for x3 x4
consts nth_closure :: "32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_closure_def:   "nth_closure y y1 = ((0 \<le> y1 \<and> bit y (nat y1)))"
  for y :: "32 word"
  and y1 :: "int"
theorem proof3'vc:
  fixes i :: "int"
  fixes n :: "32 word"
  fixes x1 :: "32 word"
  fixes x2 :: "32 word"
  fixes x3 :: "32 word"
  fixes x4 :: "32 word"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (2 :: int)"
  assumes fact2: "step0 n x1"
  assumes fact3: "step1 x1 x2"
  assumes fact4: "step2 x2 x3"
  assumes fact5: "step3 x3 x4"
  shows "uint ((x4 >> nat ((16 :: int) * i)) AND (31 :: 32 word)) = numof (nth_closure n) ((16 :: int) * i) ((16 :: int) * i + (16 :: int))"
  sorry
end
