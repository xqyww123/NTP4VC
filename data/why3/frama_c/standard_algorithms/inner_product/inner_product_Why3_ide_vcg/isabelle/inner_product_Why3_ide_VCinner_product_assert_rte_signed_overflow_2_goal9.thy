theory inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_inner_product_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_inner_product_lib.A_InnerProductAxiomatic_A_InnerProductAxiomatic" "frama_c_standard_algorithms_inner_product_lib.Compound_Compound" "frama_c_standard_algorithms_inner_product_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  shows "let x :: int = t_1 (shift a i_2); x_1 :: int = t_1 (shift a_1 i_2) in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> p_productbounds t_1 a_1 a i \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> p_innerproductbounds t_1 a_1 a i i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> is_sint32 (l_innerproduct t_1 a_1 a i_2 i_1) \<longrightarrow> x * x_1 \<le> (2147483647 :: int)"
  sorry
end
