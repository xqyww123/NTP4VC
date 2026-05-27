theory memmem_Why3_ide_VCmemmem_occr_post_part9_goal60
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal60:
  fixes a_8 :: "addr"
  fixes a_9 :: "addr"
  fixes a_5 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  shows "let x :: int = base a_8; x_1 :: int = base a_9; a_10 :: addr = shift a_5 (i_1 - i); x_2 :: int = t_1 a_10; x_3 :: int = t_1 a; a_11 :: addr = shift a_8 (0 :: int); a_12 :: addr = shift a_9 (0 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> x = base a \<longrightarrow> x_1 = base a_5 \<longrightarrow> to_uint32 (i - (1 :: int)) = (0 :: int) \<longrightarrow> \<not>x_2 = x_3 \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint8 x_3 \<longrightarrow> valid_rw t a_11 (1 :: int) \<longrightarrow> valid_rw t a_12 i_1 \<longrightarrow> separated a_12 i_1 a_11 (1 :: int) \<longrightarrow> addr_le a_6 a_10 \<longrightarrow> addr_le a_10 (shift a_7 i_1) \<longrightarrow> is_uint8 x_2 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> \<not>t_1 (shift a_4 (0 :: int)) = t_1 (shift a_3 i_3)) \<longrightarrow> \<not>(\<forall>(i_3 :: int). i_3 \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> t_1 (shift a_2 (i_3 + i_2)) = t_1 (shift a_1 i_3))"
  sorry
end
