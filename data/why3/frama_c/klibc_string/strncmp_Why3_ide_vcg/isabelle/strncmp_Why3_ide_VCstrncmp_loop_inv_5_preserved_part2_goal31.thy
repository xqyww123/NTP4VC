theory strncmp_Why3_ide_VCstrncmp_loop_inv_5_preserved_part2_goal31
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal31:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x_1 :: int = i_1 - i; a_2 :: addr = shift a_1 x_1; x_2 :: int = t_1 a_2; a_3 :: addr = shift a x_1; a_4 :: addr = shift a (0 :: int); a_5 :: addr = shift a_1 (0 :: int); a_6 :: addr = shift a i_1 in \<not>i = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> x_2 = t_1 a_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> valid_rw t a_5 i_1 \<longrightarrow> separated a_4 i_1 a_5 i_1 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> addr_le a_3 a_6 \<longrightarrow> addr_le a_2 (shift a_1 i_1) \<longrightarrow> is_sint8 x_2 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> t_1 (shift a_1 i_2) = t_1 (shift a i_2)) \<longrightarrow> addr_le (shift a ((1 :: int) + i_1 - i)) a_6"
  sorry
end
