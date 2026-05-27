theory memmove_Why3_ide_VCmemmove_loop_inv_10_established_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal16:
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> \<not>addr_le a_1 a \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> addr_le a a_2 \<and> addr_le a_2 a_2"
  sorry
end
