theory min_element_Why3_ide_VCmin_element_loop_inv_lower_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_min_element_lib.Compound_Compound" "frama_c_standard_algorithms_min_element_lib.Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_1 a_1 in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t a_1 i \<longrightarrow> p_lowerbound_1' t_1 a (0 :: int) (0 :: int) x"
  sorry
end
