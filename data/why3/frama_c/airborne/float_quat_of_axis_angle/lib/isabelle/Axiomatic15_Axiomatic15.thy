theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Compound_Compound"
begin
definition p_finite_floatvect3 :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_finite_floatvect3 mflt_0 v \<longleftrightarrow> is_finite32 (mflt_0 (shift v (0 :: int))) \<and> is_finite32 (mflt_0 (shift v (1 :: int))) \<and> is_finite32 (mflt_0 (shift v (2 :: int)))" for mflt_0 v
definition p_rvalid_floatvect3 :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_rvalid_floatvect3 malloc_0 mflt_0 v \<longleftrightarrow> p_finite_floatvect3 mflt_0 v \<and> valid_rd malloc_0 v (3 :: int)" for malloc_0 mflt_0 v
end
