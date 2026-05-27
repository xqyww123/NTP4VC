theory mismatch_Why3_ide_VCmismatch_some_not_equal_post_bound_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_mismatch_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_mismatch_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "i \<le> i_1"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "region (base a_1) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "is_sint32 (t_1 (shift a i_1))"
  assumes fact9: "is_sint32 (t_1 (shift a_1 i_1))"
  assumes fact10: "\<not>p_equalranges_1' t_1 t_1 a_1 i a"
  assumes fact11: "p_equalranges_1' t_1 t_1 a_1 i_1 a"
  assumes fact12: "valid_rd t (shift a (0 :: int)) i"
  shows "\<not>valid_rd t (shift a_1 (0 :: int)) i"
  sorry
end
