theory bitcount_BitCounting32_proveqtvc
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
definition step4 :: "32 word \<Rightarrow> 32 word \<Rightarrow> _"
  where "step4 x4 x5 \<longleftrightarrow> x5 = x4 + (x4 >> unat (16 :: 32 word))" for x4 x5
consts nth_closure :: "32 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_closure_def:   "nth_closure y y1 = ((0 \<le> y1 \<and> bit y (nat y1)))"
  for y :: "32 word"
  and y1 :: "int"
theorem prove'vc:
  fixes n :: "32 word"
  fixes x1 :: "32 word"
  fixes x2 :: "32 word"
  fixes x3 :: "32 word"
  fixes x4 :: "32 word"
  fixes x5 :: "32 word"
  assumes fact0: "step0 n x1"
  assumes fact1: "step1 x1 x2"
  assumes fact2: "step2 x2 x3"
  assumes fact3: "step3 x3 x4"
  assumes fact4: "step4 x4 x5"
  shows "uint (x5 AND (63 :: 32 word)) = numof (nth_closure n) (0 :: int) (32 :: int)"
  sorry
end
