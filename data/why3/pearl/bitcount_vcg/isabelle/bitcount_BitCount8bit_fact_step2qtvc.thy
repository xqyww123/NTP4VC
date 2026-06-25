theory bitcount_BitCount8bit_fact_step2qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
definition nth_as_bv :: "8 word \<Rightarrow> 8 word \<Rightarrow> 8 word"
  where "nth_as_bv a i = (if (bit a (unat i)) = True then 1 :: 8 word else (0 :: 8 word))" for a i
definition nth_as_int :: "8 word \<Rightarrow> int \<Rightarrow> int"
  where "nth_as_int a i = (if ((0 \<le> i \<and> bit a (nat i))) = True then 1 :: int else (0 :: int))" for a i
consts nth_closure :: "8 word \<Rightarrow> int \<Rightarrow> bool"
axiomatization where nth_closure_def:   "nth_closure y y1 = ((0 \<le> y1 \<and> bit y (nat y1)))"
  for y :: "8 word"
  and y1 :: "int"
theorem step2'vc:
  fixes i :: "int"
  fixes n :: "8 word"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (2 :: int)"
  shows "uint (((n - ((n >> unat (1 :: 8 word)) AND (85 :: 8 word)) AND (51 :: 8 word)) + ((n - ((n >> unat (1 :: 8 word)) AND (85 :: 8 word)) >> unat (2 :: 8 word)) AND (51 :: 8 word)) >> nat ((4 :: int) * i)) AND (15 :: 8 word)) = numof (nth_closure n) ((4 :: int) * i) ((4 :: int) * i + (4 :: int))"
  and "((n - ((n >> unat (1 :: 8 word)) AND (85 :: 8 word)) AND (51 :: 8 word)) + ((n - ((n >> unat (1 :: 8 word)) AND (85 :: 8 word)) >> unat (2 :: 8 word)) AND (51 :: 8 word)) >> unat (w8_of_int ((4 :: int) * i))) AND (15 :: 8 word) \<le> (4 :: 8 word)"
  sorry
end
