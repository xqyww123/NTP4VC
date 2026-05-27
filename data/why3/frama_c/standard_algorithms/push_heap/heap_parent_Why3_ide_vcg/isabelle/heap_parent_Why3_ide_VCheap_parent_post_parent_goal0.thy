theory heap_parent_Why3_ide_VCheap_parent_post_parent_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_push_heap_lib.Axiomatic_Axiomatic" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_push_heap_lib.Compound_Compound"
begin
theorem goal0:
  fixes i :: "int"
  shows "let x :: int = (i - (1 :: int)) cdiv (2 :: int) in (0 :: int) < i \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 x \<longrightarrow> x = l_heapparent i"
  sorry
end
