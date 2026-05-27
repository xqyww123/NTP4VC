theory inner_product_Why3_ide_VCinner_product_loop_inv_inner_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_inner_product_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_inner_product_lib.A_InnerProductAxiomatic_A_InnerProductAxiomatic" "frama_c_standard_algorithms_inner_product_lib.Compound_Compound" "frama_c_standard_algorithms_inner_product_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a i_2; x :: int = t_1 a_2; a_3 :: addr = shift a_1 i_2; x_1 :: int = t_1 a_3; x_2 :: int = x * x_1; x_3 :: int = l_innerproduct t_1 a_1 a i_2 i_1; x_4 :: int = x_3 + to_sint32 x_2; x_5 :: int = (1 :: int) + i_2; x_6 :: int = x_3 + x_2 in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_4 \<longrightarrow> x_4 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x_5 \<longrightarrow> p_productbounds t_1 a_1 a i \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> p_innerproductbounds t_1 a_1 a i i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_sint32 x_6 \<longrightarrow> x_6 = l_innerproduct t_1 a_1 a x_5 i_1"
  sorry
end
