theory max_element_Why3_ide_VCmax_element_loop_inv_upper_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_element_lib.Compound_Compound"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1; a_2 :: addr = shift a i_3; x_1 :: int = t_1 a_2 in (0 :: int) < i \<longrightarrow> i_3 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 ((1 :: int) + i_3) \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> (if x < x_1 then i_3 = i_2 else i_2 = i_1) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_1 \<longrightarrow> t_1 (shift a i_5) < x) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_3 \<longrightarrow> t_1 (shift a i_5) \<le> x) \<longrightarrow> t_1 (shift a i_4) \<le> t_1 (shift a i_2)"
  sorry
end
