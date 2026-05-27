theory strncpy_Why3_ide_VCstrncpy_loop_inv_6_preserved_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal9:
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_4; x_1 :: int = base a_3; x_2 :: int = offset a_4; x_3 :: int = i_1 + x_2; x_4 :: int = offset a; a_5 :: addr = shift a_4 (0 :: int); x_5 :: int = i_1 + x_2 - x_4; x_6 :: int = offset a_3; x_7 :: int = t_3 a_1; m :: addr \<Rightarrow> int = t_3(a := x_7) in \<not>x = x_1 \<longrightarrow> \<not>x_3 = x_4 \<longrightarrow> havoc t_1 t_2 a_5 ((1 :: int) + l_strnlen t_3 a_3 x_5) = t_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i + x_6 < offset a_2 \<longrightarrow> x_4 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> addr_le a_4 a \<longrightarrow> is_sint8 x_7 \<longrightarrow> p_valid_str t t_2 a_3 \<longrightarrow> p_valid_str t t_3 a_1 \<longrightarrow> p_valid_strn t t_2 a_3 i_1 \<longrightarrow> addr_le a (shift a_4 i_1) \<longrightarrow> is_uint64 x_5 \<longrightarrow> addr_le a_1 (shift a_3 (l_strnlen t_3 a_3 i_1)) \<longrightarrow> valid_rw t a_5 ((1 :: int) + l_strnlen t_2 a_3 i_1) \<longrightarrow> (if x_7 = (0 :: int) then a_2 = a_1 else shift a_1 (1 :: int) = a_2) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_6 < offset a_1 \<longrightarrow> t_3 (shift a_4 i_2) = t_3 (shift a_3 i_2)) \<longrightarrow> m (shift a_4 i) = m (shift a_3 i)"
  sorry
end
