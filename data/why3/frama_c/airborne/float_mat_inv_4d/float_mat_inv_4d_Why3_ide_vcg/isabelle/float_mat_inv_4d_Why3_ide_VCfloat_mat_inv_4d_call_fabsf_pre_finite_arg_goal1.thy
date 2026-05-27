theory float_mat_inv_4d_Why3_ide_VCfloat_mat_inv_4d_call_fabsf_pre_finite_arg_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_mat_inv_4d_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes r :: "real"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_float32 r"
  assumes fact4: "valid_rd t (shift a (0 :: int)) (16 :: int)"
  assumes fact5: "valid_rw t (shift a_1 (0 :: int)) (16 :: int)"
  shows "is_finite32 r"
  sorry
end
