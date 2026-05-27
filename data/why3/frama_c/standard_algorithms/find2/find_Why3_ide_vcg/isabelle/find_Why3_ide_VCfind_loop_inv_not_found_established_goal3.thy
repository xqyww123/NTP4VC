theory find_Why3_ide_VCfind_loop_inv_not_found_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_find2_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find2_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i_1"
  assumes fact3: "is_sint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i_1"
  shows "\<not>p_hasvalue_1' t_1 a (0 :: int) (0 :: int) i"
  sorry
end
