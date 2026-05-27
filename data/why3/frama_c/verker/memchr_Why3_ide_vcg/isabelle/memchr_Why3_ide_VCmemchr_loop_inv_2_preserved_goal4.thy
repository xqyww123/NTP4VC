theory memchr_Why3_ide_VCmemchr_loop_inv_2_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_9 :: "addr"
  fixes i_1 :: "int"
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes a_8 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_5 :: "addr"
  fixes a_2 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  shows "let x :: int = t_1 a_9; x_1 :: int = to_uint8 i_1; x_2 :: int = offset a_3; x_3 :: int = offset a_9; x_4 :: int = i + x_3 - x_2; a_10 :: addr = shift a_9 (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> region (base a_8) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_4 a_9 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint64 x_4 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_4 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_4 \<longrightarrow> addr_le a_9 (shift a_5 x_4) \<longrightarrow> (\<forall>(a_11 :: addr). addr_lt a_11 a_9 \<longrightarrow> addr_le a_2 a_11 \<longrightarrow> \<not>t_1 a_11 = x_1) \<longrightarrow> addr_le a_6 a_10 \<and> addr_le a_10 (shift a_7 x_4)"
  sorry
end
