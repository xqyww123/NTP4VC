theory bitcount_BitCount8bit_fact_nth_as_bv_is_intqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf"
begin
definition nth_as_bv :: "8 word \<Rightarrow> 8 word \<Rightarrow> 8 word"
  where "nth_as_bv a i = (if (bit a (unat i)) = True then 1 :: 8 word else (0 :: 8 word))" for a i
definition nth_as_int :: "8 word \<Rightarrow> int \<Rightarrow> int"
  where "nth_as_int a i = (if ((0 \<le> i \<and> bit a (nat i))) = True then 1 :: int else (0 :: int))" for a i
theorem nth_as_bv_is_int'vc:
  fixes a :: "8 word"
  fixes i :: "8 word"
  shows "uint (nth_as_bv a i) = nth_as_int a (uint i)"
  sorry
end
