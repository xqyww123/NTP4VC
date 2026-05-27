theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Compound_Compound"
begin
definition p_finite_floatquat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_finite_floatquat mflt_0 q \<longleftrightarrow> is_finite32 (mflt_0 (shift q (0 :: int))) \<and> is_finite32 (mflt_0 (shift q (1 :: int))) \<and> is_finite32 (mflt_0 (shift q (2 :: int))) \<and> is_finite32 (mflt_0 (shift q (3 :: int)))" for mflt_0 q
definition p_rvalid_floatquat :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_rvalid_floatquat malloc_0 mflt_0 q \<longleftrightarrow> p_finite_floatquat mflt_0 q \<and> valid_rd malloc_0 q (4 :: int)" for malloc_0 mflt_0 q
end
