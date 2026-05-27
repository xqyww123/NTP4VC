theory make_heap_Why3_ide_VCmake_heap_post_heap_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_make_heap_lib.Compound_Compound" "frama_c_standard_algorithms_make_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_make_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_make_heap_lib.A_Count_A_Count"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = (1 :: int) + i_1 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> (if (0 :: int) < i then p = False \<and> havoc t_1 t_3 a_1 i = t_2 \<and> (0 :: int) < i_1 \<and> i_1 \<le> i \<and> i \<le> i_1 \<and> p_isheap t_2 a i_1 \<and> p_multisetunchanged_1' t_2 t_3 a (0 :: int) x \<and> p_unchanged_1' t_2 t_3 a x i else t_3 = t_2) \<longrightarrow> p_isheap t_2 a i"
  sorry
end
