theory find_first_of_Why3_ide_VCfind_first_of_found_post_bound_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_first_of_lib.Compound_Compound" "frama_c_standard_algorithms_find_first_of_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i_1"
  assumes fact1: "(0 :: int) \<le> i_2"
  assumes fact2: "i_1 \<le> i_2"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "region (base a_1) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "is_uint32 i_2"
  assumes fact9: "p_hasvalueof t_1 a_1 i_1 a i"
  assumes fact10: "\<not>p_hasvalueof t_1 a_1 i_2 a i"
  assumes fact11: "valid_rd t (shift a (0 :: int)) i"
  shows "\<not>valid_rd t (shift a_1 (0 :: int)) i_1"
  sorry
end
