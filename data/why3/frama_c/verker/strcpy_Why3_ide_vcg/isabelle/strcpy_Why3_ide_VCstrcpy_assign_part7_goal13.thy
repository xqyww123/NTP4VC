theory strcpy_Why3_ide_VCstrcpy_assign_part7_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal13:
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_3; x_1 :: int = base a_2; x_2 :: int = offset a_1; x_3 :: int = offset a_2; x_4 :: int = l_strlen t_2 a_2; a_4 :: addr = shift a_3 (0 :: int); x_5 :: int = (1 :: int) + l_strlen t_3 a_2 in \<not>x = x_1 \<longrightarrow> x_2 + offset a_3 = offset a + x_3 \<longrightarrow> x_3 + x_4 = x_2 + l_strlen t_2 a_1 \<longrightarrow> havoc t_1 t_3 a_4 ((1 :: int) + x_4) = t_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_3 a \<longrightarrow> \<not>invalid t a (1 :: int) \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> p_valid_str t t_3 a_2 \<longrightarrow> addr_le a (shift a_3 x_4) \<longrightarrow> addr_le a_1 (shift a_2 x_4) \<longrightarrow> valid_rw t a_4 x_5 \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_3 < x_2 \<longrightarrow> t_2 (shift a_3 i) = t_2 (shift a_2 i)) \<longrightarrow> included a (1 :: int) a_4 x_5"
  sorry
end
