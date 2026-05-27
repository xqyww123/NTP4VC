theory make_heap_Why3_ide_VCmake_heap_call_push_heap_pre_valid_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_make_heap_lib.Compound_Compound" "frama_c_standard_algorithms_make_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_make_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_make_heap_lib.A_Count_A_Count"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; x :: int = (1 :: int) + i_1 in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) x \<longrightarrow> p_unchanged_1' a_2 t_2 a x i \<longrightarrow> valid_rw t a_1 x"
  sorry
end
