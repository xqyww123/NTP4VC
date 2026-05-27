theory find_end_Why3_ide_VCfind_end_loop_inv_result_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_end_lib.Compound_Compound" "frama_c_standard_algorithms_find_end_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i_1"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "region (base a_1) \<le> (0 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "valid_rd t (shift a (0 :: int)) i_1"
  assumes fact8: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "\<not>p_hassubrange_1' t_1 a_1 (0 :: int) (i_1 - (1 :: int)) a i_1"
  sorry
end
