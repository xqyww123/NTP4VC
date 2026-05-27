theory find_Why3_ide_VCfind_some_post_bound_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_find2_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find2_lib.Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i_1"
  assumes fact1: "(0 :: int) \<le> i_2"
  assumes fact2: "i_1 \<le> i_2"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "is_uint32 i_1"
  assumes fact6: "is_uint32 i_2"
  assumes fact7: "is_sint32 i"
  assumes fact8: "p_hasvalue_1' t_1 a (0 :: int) i_1 i"
  assumes fact9: "\<not>p_hasvalue_1' t_1 a (0 :: int) i_2 i"
  assumes fact10: "is_sint32 (t_1 (shift a i_2))"
  shows "\<not>valid_rd t (shift a (0 :: int)) i_1"
  sorry
end
