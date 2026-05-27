theory Axiomatic19_Axiomatic19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S10_RealRMat_s_S10_RealRMat_s" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Compound_Compound"
begin
definition l_l_rmat_of_floatquat_1' :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s10_realrmat_s"
  where "l_l_rmat_of_floatquat_1' mflt_0 q = (let r :: real = mflt_0 (shift q (2 :: int)); r_1 :: real = r * r; r_2 :: real = -r_1; r_3 :: real = mflt_0 (shift q (3 :: int)); r_4 :: real = r_3 * r_3; r_5 :: real = -r_4; r_6 :: real = mflt_0 (shift q (0 :: int)); r_7 :: real = r_6 * r_6; r_8 :: real = mflt_0 (shift q (1 :: int)); r_9 :: real = r_8 * r_8; r_10 :: real = r_6 * r_3; r_11 :: real = r_8 * r; r_12 :: real = r_6 * r; r_13 :: real = r_8 * r_3; r_14 :: real = -r_9; r_15 :: real = r_6 * r_8; r_16 :: real = r * r_3 in s10_realrmat_s'mk (r_7 + r_9 - r_1 - r_4) ((2 :: Real.real) * (r_11 - r_10)) ((2 :: Real.real) * (r_12 + r_13)) ((2 :: Real.real) * (r_10 + r_11)) (r_7 + r_1 - r_9 - r_4) ((2 :: Real.real) * (r_16 - r_15)) ((2 :: Real.real) * (r_13 - r_12)) ((2 :: Real.real) * (r_15 + r_16)) (r_7 + r_4 - r_9 - r_1))" for mflt_0 q
definition p_unitary_quaternion_1' :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> _"
  where "p_unitary_quaternion_1' mflt_0 q \<longleftrightarrow> (let r :: real = mflt_0 (shift q (0 :: int)); r_1 :: real = mflt_0 (shift q (1 :: int)); r_2 :: real = mflt_0 (shift q (2 :: int)); r_3 :: real = mflt_0 (shift q (3 :: int)) in r * r + r_1 * r_1 + r_2 * r_2 + r_3 * r_3 = (1 :: Real.real))" for mflt_0 q
end
