theory memmem_Why3_ide_VCmemmem_loop_inv_9_preserved_part2_goal25
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal25:
  fixes a_7 :: "addr"
  fixes a_8 :: "addr"
  fixes a_3 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes a_6 :: "addr"
  shows "let x :: int = base a_7; x_1 :: int = base a_8; a_9 :: addr = shift a_3 (i_1 - i); x_3 :: int = t_1 a_9; x_4 :: int = t_1 a; a_10 :: addr = shift a_7 (0 :: int); a_11 :: addr = shift a_8 (0 :: int) in x = base a \<longrightarrow> x_1 = base a_3 \<longrightarrow> \<not>to_uint32 (i - (1 :: int)) = (0 :: int) \<longrightarrow> \<not>x_3 = x_4 \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint8 x_4 \<longrightarrow> valid_rw t a_10 (1 :: int) \<longrightarrow> valid_rw t a_11 i_1 \<longrightarrow> separated a_11 i_1 a_10 (1 :: int) \<longrightarrow> addr_le a_4 a_9 \<longrightarrow> addr_le a_9 (shift a_5 i_1) \<longrightarrow> is_uint8 x_3 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + i < i_1 \<longrightarrow> \<not>t_1 (shift a_2 (0 :: int)) = t_1 (shift a_1 i_2)) \<longrightarrow> addr_le (shift a_3 ((1 :: int) + i_1 - i)) (shift a_6 i_1)"
  sorry
end
