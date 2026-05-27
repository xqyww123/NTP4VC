theory memmove_Why3_ide_VCmemmove_loop_inv_7_preserved_part2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x_1 :: int = i - i_1; a_3 :: addr = shift a_1 x_1; a_4 :: addr = shift a x_1; a_5 :: addr = shift a i; a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x_1 in \<not>i_1 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> addr_lt a_1 a \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> addr_lt a_3 a_4 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_4 a_5 \<longrightarrow> addr_le a_3 (shift a_1 i) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i_1 < i \<longrightarrow> a_6 (shift a_1 i_2) = t_2 (shift a i_2)) \<longrightarrow> (\<forall>(i_2 :: int). let a_7 :: addr = shift a_1 i_2 in i_2 < i \<longrightarrow> i \<le> i_2 + i_1 \<longrightarrow> a_6 a_7 = t_2 a_7) \<longrightarrow> addr_le (shift a ((1 :: int) + i - i_1)) a_5"
  sorry
end
