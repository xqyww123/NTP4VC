theory float_mat_norm_li_Why3_ide_VCfloat_mat_norm_li_loop_inv_established_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_airborne_float_mat_norm_li_lib.Axiomatic15_Axiomatic15" "frama_c_airborne_float_mat_norm_li_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "framed t_1"
  assumes fact2: "linked t"
  assumes fact3: "is_sint32 i"
  assumes fact4: "is_sint32 i_1"
  assumes fact5: "p_rvalid_float_mat_2' t t_1 a i_1 i"
  shows "(0 :: int) \<le> i_1"
  sorry
end
