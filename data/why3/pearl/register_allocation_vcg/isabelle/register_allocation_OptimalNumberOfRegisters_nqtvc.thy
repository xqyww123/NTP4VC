theory register_allocation_OptimalNumberOfRegisters_nqtvc
  imports "NTP4Verif.NTP4Verif" "./register_allocation_Spec" "./register_allocation_DWP"
begin
consts k :: "int"
axiomatization where k_def:   "(2 :: int) \<le> k"
theorem n'vc:
  fixes e :: "expr"
  shows "case e of Evar _ \<Rightarrow> True | Eneg e1 \<Rightarrow> (case e of Evar _ \<Rightarrow> False | Eneg f \<Rightarrow> f = e1 | Eadd f f1 \<Rightarrow> f = e1 \<or> f1 = e1) | Eadd e1 e2 \<Rightarrow> (case e of Evar _ \<Rightarrow> False | Eneg f \<Rightarrow> f = e1 | Eadd f f1 \<Rightarrow> f = e1 \<or> f1 = e1) \<and> (case e of Evar _ \<Rightarrow> False | Eneg f \<Rightarrow> f = e2 | Eadd f f1 \<Rightarrow> f = e2 \<or> f1 = e2)"
  sorry
end
