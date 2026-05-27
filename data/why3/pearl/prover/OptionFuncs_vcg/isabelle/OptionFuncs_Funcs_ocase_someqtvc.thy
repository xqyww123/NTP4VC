theory OptionFuncs_Funcs_ocase_someqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func"
begin
consts some :: "'a \<Rightarrow> 'a option"
axiomatization where some_def:   "some x = Some x"
  for x :: "'a"
consts ocase :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
axiomatization where ocase_def:   "ocase f d x = (case x of (None :: 'a option) \<Rightarrow> d | Some x1 \<Rightarrow> f x1)"
  for f :: "'a \<Rightarrow> 'b"
  and d :: "'b"
  and x :: "'a option"
theorem ocase_some'vc:
  fixes f :: "'a \<Rightarrow> 'b"
  fixes d :: "'b"
  fixes x :: "'a"
  shows "ocase f d (Some x) = f x"
  sorry
end
