theory hex2bin_Why3_ide_VChex2bin_assert_5_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_HexToBin_A_HexToBin"
begin
theorem goal13:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (16 :: int) * i_1; x_1 :: int = lor i x; x_2 :: int = offset a; x_3 :: int = offset a_1; x_4 :: int = t_1 a; x_5 :: int = t_1 (shift a (1 :: int)) in \<not>i_2 = (0 :: int) \<longrightarrow> x = lsl i_1 (4 :: int) \<longrightarrow> i + x = x_1 \<longrightarrow> (x_2 - x_3) cdiv (2 :: int) = (0 :: int) \<longrightarrow> (x_3 - x_2) cmod (2 :: int) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i \<le> (15 :: int) \<longrightarrow> i_1 \<le> (15 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) ((1 :: int) + i_2) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) ((1 :: int) + (2 :: int) * i_2) \<longrightarrow> (\<not>p_isxdigit x_4 \<longrightarrow> i_1 = -(1 :: int)) \<longrightarrow> (p_isxdigit x_4 \<longrightarrow> l_hex_to_bin x_4 = i_1) \<longrightarrow> (\<not>p_isxdigit x_5 \<longrightarrow> i = -(1 :: int)) \<longrightarrow> (p_isxdigit x_5 \<longrightarrow> l_hex_to_bin x_5 = i) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> p_isxdigit (t_1 a_3)) \<longrightarrow> (0 :: int) \<le> x_1 \<and> x_1 \<le> (255 :: int)"
  sorry
end
