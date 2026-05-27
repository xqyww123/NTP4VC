theory float_rmat_of_eulers_312_Why3_ide_VCfloat_rmat_of_eulers_312_call_sinf_pre_finite_arg_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "frama_c_airborne_float_rmat_of_eulers_312_lib.Compound_Compound" "frama_c_airborne_float_rmat_of_eulers_312_lib.Axiomatic15_Axiomatic15" "Why3STD.Cfloat_Cfloat"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let r :: real = t_1 (shift a_1 (0 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> valid_rw t a (9 :: int) \<longrightarrow> p_rvalid_floateulers t t_1 a_1 \<longrightarrow> is_float32 r \<longrightarrow> is_finite32 r"
  sorry
end
