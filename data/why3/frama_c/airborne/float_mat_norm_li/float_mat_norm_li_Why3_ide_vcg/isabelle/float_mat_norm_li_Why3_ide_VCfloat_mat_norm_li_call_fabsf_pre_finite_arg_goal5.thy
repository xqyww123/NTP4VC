theory float_mat_norm_li_Why3_ide_VCfloat_mat_norm_li_call_fabsf_pre_finite_arg_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_mat_norm_li_lib.Axiomatic15_Axiomatic15" "frama_c_airborne_float_mat_norm_li_lib.Compound_Compound"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes r :: "real"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let r_1 :: real = t_1 (shift (t_2 (shift a i_3)) i_2) in (0 :: Real.real) \<le> r \<longrightarrow> i_2 \<le> i \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> is_float32 r \<longrightarrow> p_rvalid_float_mat_2' t t_2 a i_1 i \<longrightarrow> is_float32 r_1 \<longrightarrow> is_finite32 r_1"
  sorry
end
