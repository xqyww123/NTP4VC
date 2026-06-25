theory sum_SumSingle_sum_of_fun_le_sum_of_abs_funqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.real_Sum" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_USingle" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_USingleLemmas"
begin
consts abs_real_fun :: "(int \<Rightarrow> usingle) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun f i = abs (to_real (f i))"
  for f :: "int \<Rightarrow> usingle"
  and i :: "int"
theorem sum_of_fun_le_sum_of_abs_fun'vc:
  fixes i :: "int"
  fixes f :: "int \<Rightarrow> usingle"
  assumes fact0: "(0 :: int) \<le> i"
  shows "abs (sum (real_fun f) (0 :: int) i) \<le> sum (abs_real_fun f) (0 :: int) i"
  sorry
end
