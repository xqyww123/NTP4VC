theory register_allocation_OptimalNumberOfRegisters_measure_nonnegqtvc
  imports "NTP4Verif.NTP4Verif" "./register_allocation_Spec" "./register_allocation_DWP"
begin
consts k :: "int"
axiomatization where k_def:   "(2 :: int) \<le> k"
fun n :: "expr \<Rightarrow> int"
  where "n (Evar x) = (1 :: int)" for x
      | "n (Eneg e1) = n e1" for e1
      | "n (Eadd e1 e2) = (let n1 :: int = n e1; n2 :: int = n e2 in if n1 = n2 then (1 :: int) + n1 else max n1 n2)" for e1 e2
fun measure :: "expr \<Rightarrow> int"
  where "measure (Evar x) = (0 :: int)" for x
      | "measure (Eneg e1) = (1 :: int) + measure e1" for e1
      | "measure (Eadd e1 e2) = (1 :: int) + (if n e2 \<le> n e1 then measure e1 + measure e2 else (1 :: int) + measure e1 + measure e2)" for e1 e2
theorem measure_nonneg'vc:
  fixes e :: "expr"
  shows "(0 :: int) \<le> measure e"
  sorry
end
