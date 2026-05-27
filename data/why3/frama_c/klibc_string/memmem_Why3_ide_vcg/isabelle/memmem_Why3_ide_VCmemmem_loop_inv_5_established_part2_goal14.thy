theory memmem_Why3_ide_VCmemmem_loop_inv_5_established_part2_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal14:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a (1 :: int)); x_1 :: int = t_1 (shift a (0 :: int)); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr = shift a_2 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_1 = (1 :: int) \<longrightarrow> x = x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> valid_rw t a_4 i \<longrightarrow> separated a_4 i a_3 i_1 \<longrightarrow> i_1 \<le> (2 :: int) + i"
  sorry
end
