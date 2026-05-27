theory strlen_Why3_ide_VCstrlen_loop_inv_2_preserved_part2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = t_1 a; x_1 :: int = base a_1; a_2 :: addr = shift a_1 (l_length t_1 a_1) in \<not>x = (0 :: int) \<longrightarrow> x_1 = base a \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + offset a_1 < offset a \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> addr_le (shift a (1 :: int)) a_2"
  sorry
end
