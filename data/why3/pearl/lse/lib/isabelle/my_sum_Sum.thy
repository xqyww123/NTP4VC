theory my_sum_Sum
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/sum_real_Sum" "../../lib/isabelle/udouble_UDouble" "Why3STD.ieee_float_RoundingMode"
begin
consts u_sum :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> udouble"
axiomatization where u_sum'def:   "if n \<le> m then u_sum a m n = uzero else u_sum a m n = uadd (u_sum a m (n - (1 :: int))) (a (n - (1 :: int)))"
  for n :: "int"
  and m :: "int"
  and a :: "int \<Rightarrow> udouble"
consts real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where real_fun'def:   "real_fun a i = to_real (a i)"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
consts abs_real_fun :: "(int \<Rightarrow> udouble) \<Rightarrow> int \<Rightarrow> real"
axiomatization where abs_real_fun'def:   "abs_real_fun a i = abs (to_real (a i))"
  for a :: "int \<Rightarrow> udouble"
  and i :: "int"
end
