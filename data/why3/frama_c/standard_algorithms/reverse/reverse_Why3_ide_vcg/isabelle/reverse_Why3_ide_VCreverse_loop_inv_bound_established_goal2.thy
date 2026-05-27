theory reverse_Why3_ide_VCreverse_loop_inv_bound_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_lib.Compound_Compound"
begin
theorem goal2:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i cdiv (2 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> x \<le> i \<and> (0 :: int) \<le> x"
  sorry
end
