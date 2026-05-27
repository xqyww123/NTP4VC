theory min_element_Why3_ide_VCmin_element_not_empty_post_min_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_min_element_lib.Compound_Compound" "frama_c_standard_algorithms_min_element_lib.Axiomatic_Axiomatic"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_1) in (0 :: int) < i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> p_lowerbound_1' t_1 a (0 :: int) i_2 x \<longrightarrow> p_strictlowerbound_1' t_1 a (0 :: int) i_1 x \<longrightarrow> p_minelement t_1 a i_2 i_1"
  sorry
end
