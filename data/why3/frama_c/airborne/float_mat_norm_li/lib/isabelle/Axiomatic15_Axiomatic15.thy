theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint"
begin
definition p_valid_size :: "int \<Rightarrow> _"
  where "p_valid_size n \<longleftrightarrow> (0 :: int) \<le> n \<and> n \<le> (2147483646 :: int)" for n
definition p_rvalid_float_mat_2' :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> addr) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_rvalid_float_mat_2' malloc_0 mptr_0 a m n \<longleftrightarrow> p_valid_size m \<and> p_valid_size n \<and> valid_rd malloc_0 (shift a (0 :: int)) m \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < m \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd malloc_0 (shift (mptr_0 (shift a i)) (0 :: int)) n)" for malloc_0 mptr_0 a m n
end
