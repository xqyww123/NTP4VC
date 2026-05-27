theory is_heap_Why3_ide_VCis_heap_post_heap_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_is_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_heap_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_heapparent i_2; a_1 :: addr = shift a x; a_2 :: addr = shift a i_2 in (0 :: int) \<le> x \<longrightarrow> x < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (1 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_isheap t_1 a i_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (if i_2 < i then i_1 = (0 :: int) \<and> t_1 a_1 < t_1 a_2 \<and> valid_rd t a_2 (1 :: int) \<and> valid_rd t a_1 (1 :: int) else i_1 = (1 :: int)) \<longrightarrow> p_isheap t_1 a i \<longleftrightarrow> \<not>i_1 = (0 :: int)"
  sorry
end
