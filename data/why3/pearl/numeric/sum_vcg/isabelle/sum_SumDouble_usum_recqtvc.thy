theory sum_SumDouble_usum_recqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.real_Sum" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_UDouble" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_UDoubleLemmas"
begin
consts abs_real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun f i = abs (to_real (f i))"
  for f :: "int \<Rightarrow> udouble"
  and i :: "int"
theorem usum_rec'vc:
  fixes n :: "int"
  fixes f :: "int \<Rightarrow> udouble"
  assumes fact0: "(0 :: int) \<le> n"
  shows "\<not>n = (0 :: int) \<longrightarrow> (let o1 :: int = n - (1 :: int) in ((0 :: int) \<le> n \<and> o1 < n) \<and> (0 :: int) \<le> o1)"
  and "\<forall>(result :: udouble). (if n = (0 :: int) then result = uzero else let o1 :: int = n - (1 :: int) in \<exists>(o2 :: udouble). abs (to_real o2 - sum (real_fun f) (0 :: int) o1) \<le> sum (abs_real_fun f) (0 :: int) o1 * (eps * real_of_int o1) \<and> result = uadd o2 (f (n - (1 :: int)))) \<longrightarrow> abs (to_real result - sum (real_fun f) (0 :: int) n) \<le> sum (abs_real_fun f) (0 :: int) n * (eps * real_of_int n)"
  sorry
end
