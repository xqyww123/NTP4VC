theory memmem_Why3_ide_VCmemmem_occr_post_part5_goal56
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal56:
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = base a_6; x_1 :: int = base a_7; x_2 :: int = t_1 (shift a_1 (1 :: int)); x_3 :: int = t_1 (shift a_1 (0 :: int)); a_8 :: addr = shift a_6 (0 :: int); a_9 :: addr = shift a_7 (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_1 = (1 :: int) \<longrightarrow> x = base a_1 \<longrightarrow> x_1 = base a \<longrightarrow> x_2 = x_3 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_1 + i_3 \<le> i \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> to_uint32 (i - i_1) < i_2 \<longrightarrow> i_1 + i_2 \<le> (2 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_2 \<longrightarrow> valid_rw t a_8 i_1 \<longrightarrow> valid_rw t a_9 i \<longrightarrow> separated a_9 i a_8 i_1 \<longrightarrow> is_uint8 (t_1 (shift a (to_uint32 ((1 :: int) + i_2)))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> t_1 (shift a_3 (i_4 + i_3)) = t_1 (shift a_2 i_4)) \<longrightarrow> \<not>(\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> (\<exists>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> (3 :: int) + i_5 \<le> i_1 \<longrightarrow> \<not>t_1 (shift a_5 ((2 :: int) + i_5 + i_4)) = t_1 (shift a_4 ((2 :: int) + i_5))))"
  sorry
end
