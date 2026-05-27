theory strstr_Why3_ide_VCstrstr_loop_inv_5_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrStr_A_StrStr"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = l_strlen t_1 a; x_1 :: int = l_strlen t_1 a_1 in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> t_1 (shift a_1 x_1) = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_lt a_2 a_1 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> is_uint64 x_1 \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_1 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i) = (0 :: int)) \<longrightarrow> \<not>p_strmatch t_1 a_2 a"
  sorry
end
