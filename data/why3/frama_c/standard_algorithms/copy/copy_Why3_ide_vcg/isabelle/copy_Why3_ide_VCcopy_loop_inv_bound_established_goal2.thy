theory copy_Why3_ide_VCcopy_loop_inv_bound_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_copy_lib.Compound_Compound"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_2 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> separated a_2 i a (1 :: int) \<longrightarrow> (0 :: int) \<le> i"
  sorry
end
