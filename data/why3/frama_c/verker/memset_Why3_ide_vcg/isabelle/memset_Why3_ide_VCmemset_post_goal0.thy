theory memset_Why3_ide_VCmemset_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  shows "let a_2 :: addr = shift a (0 :: int); x :: int = to_sint8 i in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a a \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_lt a_1 a_2 \<longrightarrow> addr_le a a_2 \<longrightarrow> valid_rw t a_2 (0 :: int) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a a_3 \<longrightarrow> t_1 a_3 = x) \<longrightarrow> t_1 a_1 = x"
  sorry
end
