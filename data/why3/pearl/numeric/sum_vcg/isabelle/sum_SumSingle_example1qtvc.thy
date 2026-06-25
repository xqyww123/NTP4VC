theory sum_SumSingle_example1qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.real_Sum" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_USingle" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_USingleLemmas"
begin
consts abs_real_fun :: "(int \<Rightarrow> usingle) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun f i = abs (to_real (f i))"
  for f :: "int \<Rightarrow> usingle"
  and i :: "int"
consts exact_f :: "int \<Rightarrow> real"
consts f' :: "int \<Rightarrow> real"
axiomatization where f'_def:   "f' i = abs (exact_f i)"
  for i :: "int"
consts f_rel_err :: "real"
consts f_cst_err :: "real"
theorem example1'vc:
  fixes n :: "int"
  fixes f :: "int \<Rightarrow> usingle"
  assumes fact0: "(0 :: int) \<le> n"
  assumes fact1: "\<forall>(i :: int). abs (to_real (f i) - exact_f i) \<le> f' i * f_rel_err"
  shows "(0 :: int) \<le> n"
  and "\<forall>(result :: usingle). abs (to_real result - sum (real_fun f) (0 :: int) n) \<le> sum (abs_real_fun f) (0 :: int) n * (eps * real_of_int n) \<longrightarrow> abs (to_real result - sum exact_f (0 :: int) n) \<le> sum f' (0 :: int) n * (f_rel_err + eps * real_of_int n * ((1 :: Real.real) + f_rel_err))"
  sorry
end
