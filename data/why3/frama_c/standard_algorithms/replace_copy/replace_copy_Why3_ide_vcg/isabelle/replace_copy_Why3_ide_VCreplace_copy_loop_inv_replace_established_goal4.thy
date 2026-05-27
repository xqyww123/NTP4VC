theory replace_copy_Why3_ide_VCreplace_copy_loop_inv_replace_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_replace_copy_lib.Compound_Compound" "frama_c_standard_algorithms_replace_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rd t a_2 i_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_2 \<longrightarrow> separated a_2 i_2 a (1 :: int) \<longrightarrow> p_replace_1' t_1 t_1 a_1 (0 :: int) a i_1 i"
  sorry
end
