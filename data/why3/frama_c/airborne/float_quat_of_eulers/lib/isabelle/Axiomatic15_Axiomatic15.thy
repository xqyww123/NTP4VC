theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Compound_Compound"
begin
definition p_finite_floateulers :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_finite_floateulers mflt_0 e \<longleftrightarrow> is_finite32 (mflt_0 (shift e (0 :: int))) \<and> is_finite32 (mflt_0 (shift e (2 :: int))) \<and> is_finite32 (mflt_0 (shift e (1 :: int)))" for mflt_0 e
definition p_rvalid_floateulers :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_rvalid_floateulers malloc_0 mflt_0 e \<longleftrightarrow> p_finite_floateulers mflt_0 e \<and> valid_rd malloc_0 e (3 :: int)" for malloc_0 mflt_0 e
end
