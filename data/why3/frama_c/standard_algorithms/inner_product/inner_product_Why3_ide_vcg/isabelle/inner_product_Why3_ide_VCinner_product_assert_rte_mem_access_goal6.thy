theory inner_product_Why3_ide_VCinner_product_assert_rte_mem_access_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_inner_product_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_inner_product_lib.A_InnerProductAxiomatic_A_InnerProductAxiomatic" "frama_c_standard_algorithms_inner_product_lib.Compound_Compound" "frama_c_standard_algorithms_inner_product_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_2"
  assumes fact2: "i_2 < i"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "region (base a_1) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "is_sint32 i_1"
  assumes fact9: "p_productbounds t_1 a_1 a i"
  assumes fact10: "p_innerproductbounds t_1 a_1 a i i_1"
  assumes fact11: "valid_rd t (shift a (0 :: int)) i"
  assumes fact12: "valid_rd t (shift a_1 (0 :: int)) i"
  assumes fact13: "is_sint32 (l_innerproduct t_1 a_1 a i_2 i_1)"
  shows "valid_rd t (shift a_1 i_2) (1 :: int)"
  sorry
end
