theory strncat_Why3_ide_VCstrncat_loop_inv_5_established_part1_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1"
begin
theorem goal11:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  shows "let x :: int = base a_2; x_1 :: int = t_1 a; x_2 :: int = l_length t_1 a_2 in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_2 \<longrightarrow> p_length_of_str_is t t_1 a_2 i_3 \<longrightarrow> ((\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_2 \<longrightarrow> \<not>t_1 (shift a_2 i_4) = (0 :: int)) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a) \<longrightarrow> ((\<exists>(i_4 :: int). t_1 (shift a_2 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < x_2) \<longrightarrow> x_1 = (0 :: int)) \<longrightarrow> ((\<exists>(i_4 :: int). t_1 (shift a_2 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < x_2) \<longrightarrow> x = base a) \<longrightarrow> ((\<exists>(i_4 :: int). t_1 (shift a_2 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < x_2) \<longrightarrow> p_exists_first_occurence_of_char t t_1 a_2 (0 :: int) (offset a - offset a_2)) \<longrightarrow> ((\<exists>(i_4 :: int). t_1 (shift a_2 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 < x_2) \<longrightarrow> addr_le a_2 a \<and> addr_le a (shift a_2 x_2)) \<longrightarrow> addr_le a_1 a_1"
  sorry
end
