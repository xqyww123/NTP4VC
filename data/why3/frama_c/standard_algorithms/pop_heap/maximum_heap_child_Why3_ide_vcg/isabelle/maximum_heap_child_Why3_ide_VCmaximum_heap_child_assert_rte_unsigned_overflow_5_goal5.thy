theory maximum_heap_child_Why3_ide_VCmaximum_heap_child_assert_rte_unsigned_overflow_5_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound"
begin
theorem goal5:
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = (2 :: int) * i; x_1 :: int = (2 :: int) + x in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> to_uint32 x \<le> (4294967293 :: int) \<longrightarrow> (2 :: int) + i \<le> i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_isheap t_1 a i_1 \<longrightarrow> is_uint32 x_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) i_1 \<longrightarrow> is_sint32 (t_1 (shift a x_1)) \<longrightarrow> (0 :: int) < i_1"
  sorry
end
