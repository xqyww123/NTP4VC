theory float_rmat_of_axis_angle_Why3_ide_VCfloat_rmat_of_axis_angle_call_cosf_pre_finite_arg_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_rmat_of_axis_angle_lib.Axiomatic15_Axiomatic15" "frama_c_airborne_float_rmat_of_axis_angle_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes r :: "real"
  fixes t_1 :: "addr \<Rightarrow> real"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_float32 r"
  assumes fact3: "p_rvalid_floatvect3 t t_1 a"
  assumes fact4: "is_float32 (t_1 (shift a (0 :: int)))"
  assumes fact5: "is_float32 (t_1 (shift a (1 :: int)))"
  assumes fact6: "is_float32 (t_1 (shift a (2 :: int)))"
  shows "is_finite32 r"
  sorry
end
