theory fill_Why3_ide_VCfill_assert_rte_mem_access_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_fill_lib.Compound_Compound" "frama_c_standard_algorithms_fill_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> p_constantrange (havoc t_1 t_2 a_1 i_1) a (0 :: int) i_2 i \<longrightarrow> valid_rw t (shift a i_2) (1 :: int)"
  sorry
end
