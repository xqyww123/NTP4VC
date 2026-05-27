theory stpcpy_Why3_ide_VCstpcpy_assign_part1_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal15:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 (0 :: int); x_2 :: int = l_strlen t_2 a; x_3 :: int = (1 :: int) + x_2; x_4 :: int = l_strlen t_3 a in \<not>x = x_1 \<longrightarrow> havoc t_1 t_3 a_2 x_3 = t_2 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> p_valid_str t t_3 a \<longrightarrow> valid_rw t a_2 ((1 :: int) + x_4) \<longrightarrow> \<not>invalid t a_2 x_3 \<longrightarrow> x_2 \<le> x_4"
  sorry
end
