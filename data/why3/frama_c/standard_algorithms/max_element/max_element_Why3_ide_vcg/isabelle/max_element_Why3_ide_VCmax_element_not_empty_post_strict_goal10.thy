theory max_element_Why3_ide_VCmax_element_not_empty_post_strict_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_element_lib.Compound_Compound"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_1) in (0 :: int) < i \<longrightarrow> i_3 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> t_1 (shift a i_4) < x) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> t_1 (shift a i_4) \<le> x) \<longrightarrow> t_1 (shift a i_2) < x"
  sorry
end
