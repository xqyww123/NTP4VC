theory memb_alloc_Why3_ide_VCmemb_alloc_complete_full_free_found_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a (1 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> p__memb_full t_3 t_2 t_1 a \<or> (\<exists>(i :: int). t_2 (shift (t_3 (shift a (2 :: int))) i) = (0 :: int) \<and> (0 :: int) \<le> i \<and> i < x)"
  sorry
end
