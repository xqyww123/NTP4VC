theory find_first_of_Why3_ide_VCfind_first_of_loop_inv_not_found_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_first_of_lib.Compound_Compound" "frama_c_standard_algorithms_find_first_of_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "is_uint32 i_1"
  assumes fact5: "valid_rd t (shift a (0 :: int)) i"
  assumes fact6: "valid_rd t (shift a_1 (0 :: int)) i_1"
  shows "\<not>p_hasvalueof t_1 a_1 (0 :: int) a i"
  sorry
end
