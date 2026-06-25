theory lse_Helpers_sum_of_fun_le_sum_of_abs_funqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.real_Sum" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_USingle" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_USingleLemmas"
begin
consts abs_fun :: "(int \<Rightarrow> real) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_fun_def:   "abs_fun f i = abs (f i)"
  for f :: "int \<Rightarrow> real"
  and i :: "int"
consts abs_real_fun :: "(int \<Rightarrow> usingle) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun f i = abs_fun (real_fun f) i"
  for f :: "int \<Rightarrow> usingle"
  and i :: "int"
theorem sum_of_fun_le_sum_of_abs_fun'vc:
  fixes b :: "int"
  fixes a :: "int"
  fixes f :: "int \<Rightarrow> usingle"
  assumes fact0: "(0 :: int) \<le> b - a"
  shows "abs (sum (real_fun f) a b) \<le> sum (abs_real_fun f) a b"
  sorry
end
