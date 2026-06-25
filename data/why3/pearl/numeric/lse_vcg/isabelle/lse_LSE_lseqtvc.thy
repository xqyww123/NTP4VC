theory lse_LSE_lseqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.real_Sum" "pearl_numeric_lib.lse_Helpers" "Why3STD.ieee_float_RoundingMode" "Why3STD.ufloat_USingle" "Why3STD.ufloat_HelperLemmas" "Why3STD.ufloat_USingleLemmas"
begin
consts exp_of_f :: "(int \<Rightarrow> usingle) \<Rightarrow> int \<Rightarrow> real"
axiomatization where exp_of_f_def:   "exp_of_f f i = exp (real_fun f i)"
  for f :: "int \<Rightarrow> usingle"
  and i :: "int"
theorem lse'vc:
  fixes n :: "int"
  fixes f' :: "int \<Rightarrow> usingle"
  fixes f :: "int \<Rightarrow> usingle"
  assumes fact0: "(0 :: int) < n"
  assumes fact1: "n < (8388608 :: int)"
  assumes fact2: "\<forall>(i :: int). f' i = exp_approx (f i)"
  shows "(0 :: int) \<le> n - (0 :: int)"
  and "let s :: usingle = usum_rec f' (0 :: int) n in abs (to_real s - sum (real_fun f') (0 :: int) n) \<le> sum (abs_real_fun f') (0 :: int) n * (eps * real_of_int (n - (0 :: int))) \<longrightarrow> (let o1 :: real = exp_error; o2 :: real = eps * real_of_int n; o3 :: int \<Rightarrow> real = abs_real_fun f' in ((\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> abs (real_fun f' i - exp_of_f f i) \<le> o1 * exp_of_f f i + (0 :: Real.real)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> exp_of_f f i - o1 * exp_of_f f i - (0 :: Real.real) \<le> o3 i \<and> o3 i \<le> exp_of_f f i + o1 * exp_of_f f i + (0 :: Real.real)) \<and> abs (to_real s - sum (real_fun f') (0 :: int) n) \<le> o2 * sum o3 (0 :: int) n + (0 :: Real.real) \<and> (0 :: Real.real) \<le> o2 \<and> (0 :: int) \<le> n) \<and> (abs (to_real s - sum (exp_of_f f) (0 :: int) n) \<le> (o1 + o2 * ((1 :: Real.real) + o1)) * sum (exp_of_f f) (0 :: int) n + ((0 :: Real.real) * real_of_int n * ((1 :: Real.real) + o2) + (0 :: Real.real)) \<longrightarrow> ((0 :: int) < n \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: Real.real) < to_real (f' i))) \<and> ((0 :: Real.real) < to_real (usum_rec f' (0 :: int) n) \<longrightarrow> (let o4 :: int \<Rightarrow> real = exp_of_f f in ((0 :: int) < n \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> (0 :: Real.real) < o4 i)) \<and> ((0 :: Real.real) < sum o4 (0 :: int) n \<and> sum o4 (0 :: int) n = sum (abs_fun o4) (0 :: int) n \<longrightarrow> (0 :: Real.real) < to_real s \<and> (let result :: usingle = log_approx s in abs (to_real result - ln (to_real s)) \<le> abs (ln (to_real s)) * log_error \<longrightarrow> abs (to_real result - ln (sum (exp_of_f f) (0 :: int) n)) \<le> abs (ln (sum (exp_of_f f) (0 :: int) n)) * log_error - ln ((1 :: Real.real) - (exp_error + real_of_int n * eps * ((1 :: Real.real) + exp_error))) * ((1 :: Real.real) + log_error)))))))"
  sorry
end
