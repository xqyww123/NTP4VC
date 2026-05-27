theory float_mat_norm_li_Why3_ide_VCfloat_mat_norm_li_loop_inv_3_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_float_mat_norm_li_lib.Axiomatic15_Axiomatic15" "frama_c_airborne_float_mat_norm_li_lib.Compound_Compound"
begin
theorem goal4:
  fixes r :: "real"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "(0 :: Real.real) \<le> r"
  assumes fact1: "i_2 \<le> i_1"
  assumes fact2: "(0 :: int) \<le> i_2"
  assumes fact3: "i_2 < i_1"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "framed t_1"
  assumes fact6: "linked t"
  assumes fact7: "is_sint32 i"
  assumes fact8: "is_sint32 i_1"
  assumes fact9: "is_sint32 i_2"
  assumes fact10: "is_float32 r"
  assumes fact11: "p_rvalid_float_mat_2' t t_1 a i_1 i"
  shows "(0 :: int) \<le> i"
  sorry
end
