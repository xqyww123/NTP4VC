theory is_heap_Why3_ide_VCis_heap_loop_inv_heap_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_is_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_heap_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = l_heapparent i_2; a_1 :: addr = shift a i_2; x_1 :: int = t_1 a_1; a_2 :: addr = shift a x; x_2 :: int = t_1 a_2; x_3 :: int = (1 :: int) + i_2 in i_2 < i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> i_2 \<le> (1 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x \<longrightarrow> p_isheap t_1 a i_2 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> \<not>i_2 cmod (2 :: int) = (0 :: int) \<or> x = i \<and> i \<le> (4294967294 :: int) \<longrightarrow> p_isheap t_1 a x_3"
  sorry
end
