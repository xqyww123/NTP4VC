theory float_quat_comp_inv_norm_shortest_Why3_ide_VCfloat_quat_comp_inv_norm_shortest_call_float_quat_normali____2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_airborne_float_quat_comp_inv_norm_shortest_lib.S3_FloatQuat_S3_FloatQuat" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat"
begin
theorem goal1:
  fixes f :: "s3_floatquat"
  fixes f_1 :: "s3_floatquat"
  fixes f_2 :: "s3_floatquat"
  fixes f_3 :: "s3_floatquat"
  shows "let r :: real = f3_floatquat_qi f; r_1 :: real = f3_floatquat_qx f; r_2 :: real = f3_floatquat_qy f; r_3 :: real = f3_floatquat_qz f; r_4 :: real = f3_floatquat_qi f_1; r_5 :: real = f3_floatquat_qx f_1; r_6 :: real = f3_floatquat_qy f_1; r_7 :: real = f3_floatquat_qz f_1; r_8 :: real = f3_floatquat_qi f_2; r_9 :: real = f3_floatquat_qx f_2; r_10 :: real = f3_floatquat_qy f_2; r_11 :: real = f3_floatquat_qz f_2; r_12 :: real = f3_floatquat_qi f_3; r_13 :: real = f3_floatquat_qx f_3; r_14 :: real = f3_floatquat_qy f_3; r_15 :: real = f3_floatquat_qz f_3 in is_finite32 r \<longrightarrow> is_finite32 r_1 \<longrightarrow> is_finite32 r_2 \<longrightarrow> is_finite32 r_3 \<longrightarrow> is_finite32 r_4 \<longrightarrow> is_finite32 r_5 \<longrightarrow> is_finite32 r_6 \<longrightarrow> is_finite32 r_7 \<longrightarrow> is_finite32 r_8 \<longrightarrow> is_finite32 r_9 \<longrightarrow> is_finite32 r_10 \<longrightarrow> is_finite32 r_11 \<longrightarrow> is_float32 r \<longrightarrow> is_float32 r_1 \<longrightarrow> is_float32 r_2 \<longrightarrow> is_float32 r_3 \<longrightarrow> is_float32 r_4 \<longrightarrow> is_float32 r_5 \<longrightarrow> is_float32 r_6 \<longrightarrow> is_float32 r_7 \<longrightarrow> is_float32 r_8 \<longrightarrow> is_float32 r_9 \<longrightarrow> is_float32 r_10 \<longrightarrow> is_float32 r_11 \<longrightarrow> is_float32 r_12 \<longrightarrow> is_float32 r_13 \<longrightarrow> is_float32 r_14 \<longrightarrow> is_float32 r_15 \<longrightarrow> is_finite32 r_12 \<and> is_finite32 r_13 \<and> is_finite32 r_14 \<and> is_finite32 r_15"
  sorry
end
