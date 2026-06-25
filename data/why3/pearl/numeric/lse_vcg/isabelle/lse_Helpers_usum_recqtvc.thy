theory lse_Helpers_usum_recqtvc
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
theorem usum_rec'vc:
  fixes b :: "int"
  fixes a :: "int"
  fixes f :: "int \<Rightarrow> usingle"
  assumes fact0: "(0 :: int) \<le> b - a"
  shows "let o1 :: int = b - a in (\<not>o1 \<le> (0 :: int) \<longrightarrow> \<not>b - a = (1 :: int) \<longrightarrow> (let o2 :: int = b - (1 :: int) in ((0 :: int) \<le> b - a \<and> o2 - a < b - a) \<and> (0 :: int) \<le> o2 - a)) \<and> (\<forall>(result :: usingle). (if o1 \<le> (0 :: int) then result = uzero else if b - a = (1 :: int) then result = f (b - (1 :: int)) else let o2 :: int = b - (1 :: int) in \<exists>(o3 :: usingle). abs (to_real o3 - sum (real_fun f) a o2) \<le> sum (abs_real_fun f) a o2 * (eps * real_of_int (o2 - a)) \<and> result = uadd o3 (f (b - (1 :: int)))) \<longrightarrow> abs (to_real result - sum (real_fun f) a b) \<le> sum (abs_real_fun f) a b * (eps * real_of_int (b - a)))"
  sorry
end
