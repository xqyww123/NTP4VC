theory push_heap_Why3_ide_VCpush_heap_assign_normal_part3_goal25
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_push_heap_lib.Compound_Compound" "frama_c_standard_algorithms_push_heap_lib.Axiomatic_Axiomatic"
begin
theorem goal25:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = l_heapparent x; a_1 :: addr = shift a x_1; x_2 :: int = t_1 a_1; a_2 :: addr = shift a x; x_3 :: int = t_1 a_2; a_3 :: addr = shift a (0 :: int); a_4 :: addr = shift a (to_uint32 x) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_2 < x_3 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_isheap t_1 a x \<longrightarrow> is_sint32 x_3 \<longrightarrow> \<not>invalid t a_2 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> included a_2 (1 :: int) a_3 i"
  sorry
end
