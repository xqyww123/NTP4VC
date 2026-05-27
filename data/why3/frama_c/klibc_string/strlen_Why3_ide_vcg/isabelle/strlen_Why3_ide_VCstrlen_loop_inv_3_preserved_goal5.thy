theory strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = t_1 a; x_1 :: int = base a_1; x_2 :: int = offset a_1; x_3 :: int = offset a in \<not>x = (0 :: int) \<longrightarrow> x_1 = base a \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> i_2 + x_2 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> addr_le a (shift a_1 (l_length t_1 a_1)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_2 < x_3 \<longrightarrow> \<not>t_1 (shift a_1 i_3) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)"
  sorry
end
