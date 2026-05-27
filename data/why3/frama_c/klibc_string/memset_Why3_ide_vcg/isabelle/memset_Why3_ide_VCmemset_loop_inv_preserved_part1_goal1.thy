theory memset_Why3_ide_VCmemset_loop_inv_preserved_part1_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_2 \<longrightarrow> i_2 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i < i_1 \<longrightarrow> havoc t_1 t_2 a_1 (i_1 - i) (shift a i_3) = i_2) \<longrightarrow> to_uint32 (i - (1 :: int)) \<le> i_1"
  sorry
end
