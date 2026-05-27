theory strstr_Why3_ide_VCstrstr_call_memcmp_pre_5_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrStr_A_StrStr"
begin
theorem goal15:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_6 :: "addr"
  fixes a_5 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let x :: int = l_strlen t_1 a_4; x_1 :: int = l_strlen t_1 a_6; a_7 :: addr = shift a_6 x_1; x_2 :: int = offset a_6; x_3 :: int = offset a_5 in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a_4 x) = (0 :: int) \<longrightarrow> t_1 a_7 = (0 :: int) \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> x_3 + x \<le> x_2 + x_1 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_6 a_5 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> p_valid_str t t_1 a_5 \<longrightarrow> p_valid_str t t_1 a_6 \<longrightarrow> is_uint64 x \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a_5 a_7 \<longrightarrow> is_uint64 (x_2 + x_1 - x_3) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_1 (shift a_4 i) = (0 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> \<not>t_1 (shift a_6 i) = (0 :: int)) \<longrightarrow> (\<forall>(a_8 :: addr). addr_lt a_8 a_5 \<longrightarrow> addr_le a_6 a_8 \<longrightarrow> \<not>p_strmatch t_1 a_8 a_4) \<longrightarrow> base a_3 = base a_2 \<longleftrightarrow> base a_1 = base a"
  sorry
end
