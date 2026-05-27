theory random_shuffle_Why3_ide_VCrandom_shuffle_assign_exit_part4_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_random_shuffle_lib.Compound_Compound" "frama_c_standard_algorithms_random_shuffle_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_random_shuffle_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_random_shuffle_lib.A_Count_A_Count"
begin
theorem goal7:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; a_3 :: addr = shift a (to_uint32 ((1 :: int) + i)); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1 in (0 :: int) < i_1 \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> p_unchanged_1' a_4 t_2 a i_2 i_1 \<longrightarrow> p_multisetunchanged_1' a_4 t_2 a (0 :: int) i_2 \<longrightarrow> (\<not>invalid t a_2 (1 :: int) \<longrightarrow> included a_2 (1 :: int) a_1 i_1) \<and> (\<not>invalid t a_3 (1 :: int) \<longrightarrow> included a_3 (1 :: int) a_1 i_1)"
  sorry
end
