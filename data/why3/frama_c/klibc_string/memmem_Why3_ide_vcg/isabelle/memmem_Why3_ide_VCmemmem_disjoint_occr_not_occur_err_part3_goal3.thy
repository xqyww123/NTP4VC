theory memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part3_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal3:
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let a_6 :: addr = shift a_4 (0 :: int); a_7 :: addr = shift a_5 (0 :: int) in (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_6 i_1 \<longrightarrow> valid_rw t a_7 i \<longrightarrow> separated a_7 i a_6 i_1 \<longrightarrow> i = (0 :: int) \<or> i_1 = (0 :: int) \<or> i < i_1 \<or> (\<forall>(i_2 :: int). i_2 < (0 :: int) \<or> i < i_2 + i_1 \<or> (\<exists>(i_3 :: int). \<not>t_1 (shift a_1 (i_3 + i_2)) = t_1 (shift a i_3) \<and> (0 :: int) \<le> i_3 \<and> i_3 < i_1)) \<or> (\<exists>(i_2 :: int). (0 :: int) \<le> i_2 \<and> i_2 + i_1 \<le> i \<and> (\<forall>(i_3 :: int). t_1 (shift a_3 (i_3 + i_2)) = t_1 (shift a_2 i_3) \<or> i_3 < (0 :: int) \<or> i_1 \<le> i_3))"
  sorry
end
