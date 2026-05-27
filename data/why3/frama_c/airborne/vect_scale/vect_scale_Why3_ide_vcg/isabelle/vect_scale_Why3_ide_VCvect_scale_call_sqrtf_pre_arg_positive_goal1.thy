theory vect_scale_Why3_ide_VCvect_scale_call_sqrtf_pre_arg_positive_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_airborne_vect_scale_lib.S2_FloatVect3_S2_FloatVect3" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat"
begin
theorem goal1:
  fixes f :: "s2_floatvect3"
  shows "let r :: real = f2_floatvect3_x f; r_1 :: real = f2_floatvect3_y f in is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> (0 :: Real.real) \<le> r * r + r_1 * r_1"
  sorry
end
