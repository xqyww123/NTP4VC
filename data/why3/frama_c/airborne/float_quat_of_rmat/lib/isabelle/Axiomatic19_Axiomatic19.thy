theory Axiomatic19_Axiomatic19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "S10_RealRMat_s_S10_RealRMat_s" "Why3STD.Memory_Memory" "Axiomatic17_Axiomatic17" "Compound_Compound" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "S11_RealQuat_s_S11_RealQuat_s" "Why3STD.Square_Square"
begin
definition l_trace_1' :: "s10_realrmat_s \<Rightarrow> real"
  where "l_trace_1' rmat_0 = f10_realrmat_s_a00 rmat_0 + f10_realrmat_s_a11 rmat_0 + f10_realrmat_s_a22 rmat_0" for rmat_0
definition l_trace_2' :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> real"
  where "l_trace_2' mflt_0 rmat_0 = l_trace_1' (l_l_rmat_of_floatrmat mflt_0 rmat_0)" for mflt_0 rmat_0
definition l_l_floatquat_of_rmat_trace_pos_1' :: "s10_realrmat_s \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_trace_pos_1' rmat_0 = (let r :: real = (1 :: Real.real) / (2 :: Real.real) / sqrt ((1 :: Real.real) + l_trace_1' rmat_0) in s11_realquat_s'mk ((1 :: Real.real) / (4 :: Real.real) / r) ((f10_realrmat_s_a21 rmat_0 - f10_realrmat_s_a12 rmat_0) * r) ((f10_realrmat_s_a02 rmat_0 - f10_realrmat_s_a20 rmat_0) * r) ((f10_realrmat_s_a10 rmat_0 - f10_realrmat_s_a01 rmat_0) * r))" for rmat_0
definition l_l_floatquat_of_rmat_trace_pos_t :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_trace_pos_t mflt_0 rmat_0 = l_l_floatquat_of_rmat_trace_pos_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0))" for mflt_0 rmat_0
definition l_l_floatquat_of_rmat_0_max_1' :: "s10_realrmat_s \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_0_max_1' rmat_0 = (let r :: real = sqrt ((1 :: Real.real) + f10_realrmat_s_a00 rmat_0 - f10_realrmat_s_a11 rmat_0 - f10_realrmat_s_a22 rmat_0); r_1 :: real = (2 :: Real.real) * r in s11_realquat_s'mk ((f10_realrmat_s_a21 rmat_0 - f10_realrmat_s_a12 rmat_0) / r_1) ((1 :: Real.real) / (2 :: Real.real) * r) ((f10_realrmat_s_a01 rmat_0 + f10_realrmat_s_a10 rmat_0) / r_1) ((f10_realrmat_s_a02 rmat_0 + f10_realrmat_s_a20 rmat_0) / r_1))" for rmat_0
definition l_l_floatquat_of_rmat_0_max_t :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_0_max_t mflt_0 rmat_0 = l_l_floatquat_of_rmat_0_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0))" for mflt_0 rmat_0
definition l_l_floatquat_of_rmat_1_max_1' :: "s10_realrmat_s \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_1_max_1' rmat_0 = (let r :: real = sqrt ((1 :: Real.real) + f10_realrmat_s_a11 rmat_0 - f10_realrmat_s_a00 rmat_0 - f10_realrmat_s_a22 rmat_0); r_1 :: real = (2 :: Real.real) * r in s11_realquat_s'mk ((f10_realrmat_s_a02 rmat_0 - f10_realrmat_s_a20 rmat_0) / r_1) ((f10_realrmat_s_a01 rmat_0 + f10_realrmat_s_a10 rmat_0) / r_1) ((1 :: Real.real) / (2 :: Real.real) * r) ((f10_realrmat_s_a12 rmat_0 + f10_realrmat_s_a21 rmat_0) / r_1))" for rmat_0
definition l_l_floatquat_of_rmat_1_max_t :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_1_max_t mflt_0 rmat_0 = l_l_floatquat_of_rmat_1_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0))" for mflt_0 rmat_0
definition l_l_floatquat_of_rmat_2_max_1' :: "s10_realrmat_s \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_2_max_1' rmat_0 = (let r :: real = sqrt ((1 :: Real.real) + f10_realrmat_s_a22 rmat_0 - f10_realrmat_s_a00 rmat_0 - f10_realrmat_s_a11 rmat_0); r_1 :: real = (2 :: Real.real) * r in s11_realquat_s'mk ((f10_realrmat_s_a10 rmat_0 - f10_realrmat_s_a01 rmat_0) / r_1) ((f10_realrmat_s_a02 rmat_0 + f10_realrmat_s_a20 rmat_0) / r_1) ((f10_realrmat_s_a12 rmat_0 + f10_realrmat_s_a21 rmat_0) / r_1) ((1 :: Real.real) / (2 :: Real.real) * r))" for rmat_0
definition l_l_floatquat_of_rmat_2_max_t :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s11_realquat_s"
  where "l_l_floatquat_of_rmat_2_max_t mflt_0 rmat_0 = l_l_floatquat_of_rmat_2_max_1' (l_transpose (l_l_rmat_of_floatrmat mflt_0 rmat_0))" for mflt_0 rmat_0
end
