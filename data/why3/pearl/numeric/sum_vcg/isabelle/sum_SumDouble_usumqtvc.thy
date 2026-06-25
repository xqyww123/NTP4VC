theory sum_SumDouble_usumqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.real_Sum" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_UDouble" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_UDoubleLemmas"
begin
consts abs_real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun_def:   "abs_real_fun f i = abs (to_real (f i))"
  for f :: "int \<Rightarrow> udouble"
  and i :: "int"
theorem usum'vc:
  fixes n :: "int"
  fixes f :: "int \<Rightarrow> udouble"
  assumes fact0: "(0 :: int) \<le> n"
  shows "let o1 :: int = n - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> abs (to_real u0 - sum (real_fun f) (0 :: int) (0 :: int)) \<le> sum (abs_real_fun f) (0 :: int) (0 :: int) * (eps * real_of_int (0 :: int)) \<and> (\<forall>(s :: udouble). (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o1) \<and> abs (to_real s - sum (real_fun f) (0 :: int) i) \<le> sum (abs_real_fun f) (0 :: int) i * (eps * real_of_int i) \<longrightarrow> abs (to_real (uadd s (f i)) - sum (real_fun f) (0 :: int) (i + (1 :: int))) \<le> sum (abs_real_fun f) (0 :: int) (i + (1 :: int)) * (eps * real_of_int (i + (1 :: int)))) \<and> (abs (to_real s - sum (real_fun f) (0 :: int) (o1 + (1 :: int))) \<le> sum (abs_real_fun f) (0 :: int) (o1 + (1 :: int)) * (eps * real_of_int (o1 + (1 :: int))) \<longrightarrow> abs (to_real s - sum (real_fun f) (0 :: int) n) \<le> sum (abs_real_fun f) (0 :: int) n * (eps * real_of_int n)))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> abs (to_real u0 - sum (real_fun f) (0 :: int) n) \<le> sum (abs_real_fun f) (0 :: int) n * (eps * real_of_int n))"
  sorry
end
