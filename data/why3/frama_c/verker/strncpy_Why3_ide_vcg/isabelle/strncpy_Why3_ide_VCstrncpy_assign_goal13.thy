theory strncpy_Why3_ide_VCstrncpy_assign_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal13:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 (0 :: int); x_2 :: int = l_strnlen t_2 a i_1; x_3 :: int = (1 :: int) + x_2; x_4 :: int = l_strnlen t_3 a i in \<not>x = x_1 \<longrightarrow> havoc t_1 t_3 a_2 x_3 = t_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_3 a \<longrightarrow> p_valid_strn t t_3 a i \<longrightarrow> valid_rw t a_2 ((1 :: int) + x_4) \<longrightarrow> \<not>invalid t a_2 x_3 \<longrightarrow> x_2 \<le> x_4"
  sorry
end
