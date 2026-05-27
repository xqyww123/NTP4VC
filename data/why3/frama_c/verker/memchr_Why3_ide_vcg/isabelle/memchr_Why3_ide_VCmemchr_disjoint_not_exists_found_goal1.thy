theory memchr_Why3_ide_VCmemchr_disjoint_not_exists_found_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal1:
  fixes i_1 :: "int"
  fixes a_6 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  shows "let x :: int = to_uint8 i_1 in region (base a_6) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> (\<exists>(a_7 :: addr). t_1 a_7 = x \<and> addr_le a_2 a_7 \<and> addr_lt a_7 (shift a_3 i)) \<or> (\<forall>(a_7 :: addr). \<not>t_1 a_7 = x \<or> \<not>addr_le a_4 a_7 \<or> \<not>addr_lt a_7 (shift a_5 i))"
  sorry
end
