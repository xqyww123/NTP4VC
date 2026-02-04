theory my_lse_LSE
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/udouble_UDouble" "Why3STD.ieee_float_RoundingMode" "../../lib/isabelle/my_exp_log_ExpLogLemmas" "../../lib/isabelle/my_exp_log_ExpLogApprox" "../../lib/isabelle/sum_real_Sum" "../../lib/isabelle/my_sum_Sum" "../../lib/isabelle/my_sum_Bound" "../../lib/isabelle/my_sum_Combine"
begin
consts exp_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where exp_fun'def:   "exp_fun a i = exp (real_fun a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
consts u_exp_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> udouble"
axiomatization where u_exp_fun'def:   "u_exp_fun a i = u_exp (a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
definition u_sum_of_u_exp :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> udouble"
  where "u_sum_of_u_exp a m n = u_sum (u_exp_fun a) m n" for a m n
definition lse_exact :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
  where "lse_exact f size = ln (sum (exp_fun f) (0 :: int) size)" for f size
end
