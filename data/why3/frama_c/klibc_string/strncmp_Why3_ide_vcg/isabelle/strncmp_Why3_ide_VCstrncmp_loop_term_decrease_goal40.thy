theory strncmp_Why3_ide_VCstrncmp_loop_term_decrease_goal40
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal40:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 - i; a_2 :: addr = shift a x; x_1 :: int = t_1 a_2; a_3 :: addr = shift a_1 x; a_4 :: addr = shift a (0 :: int); a_5 :: addr = shift a_1 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> t_1 a_3 = x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> valid_rw t a_5 i_1 \<longrightarrow> separated a_5 i_1 a_4 i_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 (shift a i_1) \<longrightarrow> addr_le a_3 (shift a_1 i_1) \<longrightarrow> is_sint8 x_1 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> t_1 (shift a_1 i_2) = t_1 (shift a i_2)) \<longrightarrow> to_uint32 (i - (1 :: int)) < i"
  sorry
end
