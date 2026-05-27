theory memchr_Why3_ide_VCmemchr_found_post_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_11 :: "addr"
  fixes a_5 :: "addr"
  fixes a_9 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_8 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_6 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_7 :: "addr"
  fixes a_10 :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = t_1 a_11; x_1 :: int = offset a_5; x_2 :: int = offset a_9; x_3 :: int = i + x_2 - x_1 in x = to_uint8 i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> region (base a_8) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a_11 \<longrightarrow> addr_le a_6 a_9 \<longrightarrow> is_uint64 x_3 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_3 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_3 \<longrightarrow> addr_lt a_11 (shift a_3 x_3) \<longrightarrow> addr_le a_9 (shift a_7 x_3) \<longrightarrow> (if i = (0 :: int) then Mk_addr (0 :: int) (0 :: int) = a_10 else x = t_1 a_9) \<longrightarrow> (\<forall>(a_12 :: addr). addr_lt a_12 a_9 \<longrightarrow> addr_le a_4 a_12 \<longrightarrow> \<not>x = t_1 a_12) \<longrightarrow> addr_le a_8 a_10 \<and> addr_le a_10 (shift a_8 x_3)"
  sorry
end
