theory hex2bin_Why3_ide_VChex2bin_assert_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_HexToBin_A_HexToBin"
begin
theorem goal10:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a; x_1 :: int = offset a_1; x_2 :: int = t_1 a; x_3 :: int = t_1 (shift a (1 :: int)) in \<not>i_2 = (0 :: int) \<longrightarrow> (x - x_1) cdiv (2 :: int) = (0 :: int) \<longrightarrow> (x_1 - x) cmod (2 :: int) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) ((1 :: int) + i_2) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) ((1 :: int) + (2 :: int) * i_2) \<longrightarrow> (p_isxdigit x_2 \<longrightarrow> i_1 \<le> (15 :: int)) \<longrightarrow> (\<not>p_isxdigit x_2 \<longrightarrow> i_1 = -(1 :: int)) \<longrightarrow> (p_isxdigit x_2 \<longrightarrow> l_hex_to_bin x_2 = i_1) \<longrightarrow> (p_isxdigit x_3 \<longrightarrow> i \<le> (15 :: int)) \<longrightarrow> (\<not>p_isxdigit x_3 \<longrightarrow> i = -(1 :: int)) \<longrightarrow> (p_isxdigit x_3 \<longrightarrow> l_hex_to_bin x_3 = i) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> p_isxdigit (t_1 a_3)) \<longrightarrow> i \<le> (15 :: int) \<and> i_1 \<le> (15 :: int)"
  sorry
end
