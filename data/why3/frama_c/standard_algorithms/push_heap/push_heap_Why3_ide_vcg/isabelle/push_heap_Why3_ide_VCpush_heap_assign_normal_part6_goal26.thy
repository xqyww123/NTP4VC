theory push_heap_Why3_ide_VCpush_heap_assign_normal_part6_goal26
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_push_heap_lib.Compound_Compound" "frama_c_standard_algorithms_push_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_push_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_push_heap_lib.A_Count_A_Count"
begin
theorem goal26:
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes p :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = i_1 - (1 :: int); x_1 :: int = l_heapparent x; a_1 :: addr = shift a x_1; x_2 :: int = t_2 a_1; a_2 :: addr = shift a x; x_3 :: int = t_2 a_2; a_3 :: addr = shift a (0 :: int); a_4 :: addr = shift a i_4; a_5 :: addr = shift a (to_uint32 x); x_4 :: int = t_3 a_4; a_6 :: addr = shift a i in (0 :: int) < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_2 < x_3 \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> \<not>invalid t a_4 (1 :: int) \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_isheap t_2 a x \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> (if (0 :: int) < x_1 then p = False \<and> i_4 = i_3 \<and> i_5 = i_3 \<and> i_5 = i_4 \<and> l_heapparent i_4 = i \<and> x_1 = i_2 \<and> havoc t_1 (t_2(a_2 := t_2 (shift a i_2))) a_3 i_1 = t_3 \<and> (0 :: int) \<le> i_4 \<and> x_4 < x_3 \<and> (2 :: int) + i_4 \<le> i_1 \<and> p_isheap t_3 a i_1 \<and> p_multisetadd t_3 t_2 a i_1 x_4 \<and> p_multisetminus t_3 t_2 a i_1 x_3 \<and> p_multisetretainrest_3' t_3 t_2 a i_1 x_3 x_4 \<and> (i_4 \<le> (0 :: int) \<or> x_3 \<le> t_3 a_6 \<and> valid_rd t a_6 (1 :: int)) else x_1 = i_4) \<longrightarrow> included a_4 (1 :: int) a_3 i_1"
  sorry
end
