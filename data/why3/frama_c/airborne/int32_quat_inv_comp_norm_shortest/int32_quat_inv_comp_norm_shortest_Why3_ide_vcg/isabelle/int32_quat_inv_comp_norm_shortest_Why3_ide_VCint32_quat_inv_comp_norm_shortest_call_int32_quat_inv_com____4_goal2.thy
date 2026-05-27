theory int32_quat_inv_comp_norm_shortest_Why3_ide_VCint32_quat_inv_comp_norm_shortest_call_int32_quat_inv_com____4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_airborne_int32_quat_inv_comp_norm_shortest_lib.Compound_Compound" "frama_c_airborne_int32_quat_inv_comp_norm_shortest_lib.Axiomatic15_Axiomatic15"
begin
theorem goal2:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "separated a_1 (4 :: int) a (4 :: int)"
  assumes fact4: "is_sint32 (t_1 (shift a (0 :: int)))"
  assumes fact5: "is_sint32 (t_1 (shift a_1 (0 :: int)))"
  assumes fact6: "is_sint32 (t_1 (shift a (1 :: int)))"
  assumes fact7: "is_sint32 (t_1 (shift a_1 (1 :: int)))"
  assumes fact8: "is_sint32 (t_1 (shift a (2 :: int)))"
  assumes fact9: "is_sint32 (t_1 (shift a_1 (2 :: int)))"
  assumes fact10: "is_sint32 (t_1 (shift a (3 :: int)))"
  assumes fact11: "is_sint32 (t_1 (shift a_1 (3 :: int)))"
  assumes fact12: "p_rvalid_bound_int32quat t t_1 a (13777 :: int)"
  assumes fact13: "p_rvalid_bound_int32quat t t_1 a_1 (13777 :: int)"
  shows "valid_rd t a (4 :: int)"
  sorry
end
