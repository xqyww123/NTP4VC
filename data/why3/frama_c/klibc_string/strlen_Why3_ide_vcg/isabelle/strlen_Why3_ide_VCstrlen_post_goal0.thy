theory strlen_Why3_ide_VCstrlen_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = base a_1; x_1 :: int = offset a; x_2 :: int = offset a_1; x_3 :: int = l_length t_1 a_1 in t_1 a = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_length_of_str_is t t_1 a_1 i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> is_sint32 (x_1 - x_2) \<longrightarrow> addr_le a (shift a_1 x_3) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x_2 < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> x_2 + x_3 = x_1"
  sorry
end
