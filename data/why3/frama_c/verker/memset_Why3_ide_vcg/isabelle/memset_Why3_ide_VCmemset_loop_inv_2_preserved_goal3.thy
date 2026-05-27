theory memset_Why3_ide_VCmemset_loop_inv_2_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal3:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i; a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a \<longrightarrow> addr_le a a_1 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a \<longrightarrow> addr_le a a_4 \<longrightarrow> havoc t_1 t_2 a_2 i a_4 = to_sint8 i_1) \<longrightarrow> addr_le a a_3 \<and> addr_le a_3 a_1"
  sorry
end
