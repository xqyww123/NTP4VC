theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Compound_Compound" "S5_FloatRMat_S5_FloatRMat"
begin
definition p_finite_floatrmat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_finite_floatrmat mflt_0 rm_0 \<longleftrightarrow> (let a :: addr = shift rm_0 (0 :: int) in is_finite32 (mflt_0 (shift a (0 :: int))) \<and> is_finite32 (mflt_0 (shift a (1 :: int))) \<and> is_finite32 (mflt_0 (shift a (2 :: int))) \<and> is_finite32 (mflt_0 (shift a (3 :: int))) \<and> is_finite32 (mflt_0 (shift a (4 :: int))) \<and> is_finite32 (mflt_0 (shift a (5 :: int))) \<and> is_finite32 (mflt_0 (shift a (6 :: int))) \<and> is_finite32 (mflt_0 (shift a (7 :: int))) \<and> is_finite32 (mflt_0 (shift a (8 :: int))))" for mflt_0 rm_0
definition p_rvalid_floatrmat :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_rvalid_floatrmat malloc_0 mflt_0 rm_0 \<longleftrightarrow> p_finite_floatrmat mflt_0 rm_0 \<and> valid_rd malloc_0 rm_0 (9 :: int)" for malloc_0 mflt_0 rm_0
definition p_finite_floatrates :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_finite_floatrates mflt_0 r \<longleftrightarrow> is_finite32 (mflt_0 (shift r (0 :: int))) \<and> is_finite32 (mflt_0 (shift r (1 :: int))) \<and> is_finite32 (mflt_0 (shift r (2 :: int)))" for mflt_0 r
definition p_rvalid_floatrates :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_rvalid_floatrates malloc_0 mflt_0 r \<longleftrightarrow> p_finite_floatrates mflt_0 r \<and> valid_rd malloc_0 r (3 :: int)" for malloc_0 mflt_0 r
end
