theory is_heap_Why3_ide_VCis_heap_assert_rte_unsigned_overflow_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_is_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_heap_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_heapparent i_1; a_1 :: addr = shift a i_1; x_1 :: int = t_1 a_1; a_2 :: addr = shift a x; x_2 :: int = t_1 a_2 in i_1 cmod (2 :: int) = (0 :: int) \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> i_1 \<le> (1 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_isheap t_1 a i_1 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> x \<le> (4294967294 :: int)"
  sorry
end
