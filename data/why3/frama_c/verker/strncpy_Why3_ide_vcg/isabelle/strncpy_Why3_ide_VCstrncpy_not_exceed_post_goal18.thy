theory strncpy_Why3_ide_VCstrncpy_not_exceed_post_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal18:
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = base a_3; x_1 :: int = base a_1; a_4 :: addr = shift a_1 (0 :: int); x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = x_3 - x_2 in \<not>x = x_1 \<longrightarrow> havoc t_1 t_2 a_4 ((1 :: int) + l_strnlen t_3 a_3 (0 :: int)) = t_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i + x_2 \<le> x_3 \<longrightarrow> x_3 < x_2 + l_strlen t_2 a_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_valid_str t t_2 a_3 \<longrightarrow> p_valid_str t t_3 a_2 \<longrightarrow> is_uint64 x_4 \<longrightarrow> p_valid_strn t t_2 a_3 x_4 \<longrightarrow> p_valid_strn t t_3 a x_4 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> addr_le a_2 (shift a_3 (l_strnlen t_3 a_3 x_4)) \<longrightarrow> valid_rw t a_4 ((1 :: int) + l_strnlen t_2 a_3 x_4) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + offset a_3 < offset a_2 \<longrightarrow> t_3 (shift a_3 i_1) = t_3 (shift a_1 i_1)) \<longrightarrow> t_3 (shift a_3 i) = t_3 (shift a_1 i)"
  sorry
end
