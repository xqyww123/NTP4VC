theory strncpy_Why3_ide_VCstrncpy_loop_inv_2_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal3:
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  shows "let x :: int = base a_3; x_1 :: int = base a_2; x_2 :: int = offset a_3; x_3 :: int = i + x_2; x_4 :: int = offset a; a_4 :: addr = shift a_3 (0 :: int); x_5 :: int = i + x_2 - x_4; a_5 :: addr = shift a_3 i; a_6 :: addr = shift a (1 :: int) in \<not>x = x_1 \<longrightarrow> \<not>x_3 = x_4 \<longrightarrow> havoc t_1 t_2 a_4 ((1 :: int) + l_strnlen t_3 a_2 x_5) = t_3 \<longrightarrow> x_2 \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_4 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_3 a \<longrightarrow> is_sint8 (t_3 a_1) \<longrightarrow> p_valid_str t t_2 a_2 \<longrightarrow> p_valid_str t t_3 a_1 \<longrightarrow> p_valid_strn t t_2 a_2 i \<longrightarrow> addr_le a a_5 \<longrightarrow> is_uint64 x_5 \<longrightarrow> addr_le a_1 (shift a_2 (l_strnlen t_3 a_2 i)) \<longrightarrow> valid_rw t a_4 ((1 :: int) + l_strnlen t_2 a_2 i) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + offset a_2 < offset a_1 \<longrightarrow> t_3 (shift a_3 i_1) = t_3 (shift a_2 i_1)) \<longrightarrow> addr_le a_3 a_6 \<and> addr_le a_6 a_5"
  sorry
end
