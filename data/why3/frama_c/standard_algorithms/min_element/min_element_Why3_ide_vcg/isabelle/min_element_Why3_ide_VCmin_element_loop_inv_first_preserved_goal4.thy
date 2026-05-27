theory min_element_Why3_ide_VCmin_element_loop_inv_first_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_min_element_lib.Compound_Compound" "frama_c_standard_algorithms_min_element_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2; x :: int = t_1 a_1; a_2 :: addr = shift a i_1; x_1 :: int = t_1 a_2; a_3 :: addr = shift a (0 :: int) in (0 :: int) < i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x < x_1 \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 (t_1 a_3) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_lowerbound_1' t_1 a (0 :: int) i_2 x_1 \<longrightarrow> p_strictlowerbound_1' t_1 a (0 :: int) i_1 x_1 \<longrightarrow> p_strictlowerbound_1' t_1 a (0 :: int) i_2 x"
  sorry
end
