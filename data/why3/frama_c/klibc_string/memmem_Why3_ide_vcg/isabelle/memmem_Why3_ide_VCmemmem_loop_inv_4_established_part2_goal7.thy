theory memmem_Why3_ide_VCmemmem_loop_inv_4_established_part2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  shows "let x :: int = t_1 (shift a_1 (1 :: int)); x_1 :: int = t_1 (shift a_1 (0 :: int)); x_2 :: int = base a_3; a_4 :: addr = shift a_2 (0 :: int); a_5 :: addr = shift a_3 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_1 = (1 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_5 i a_4 i_1 \<longrightarrow> x_2 = base a"
  sorry
end
