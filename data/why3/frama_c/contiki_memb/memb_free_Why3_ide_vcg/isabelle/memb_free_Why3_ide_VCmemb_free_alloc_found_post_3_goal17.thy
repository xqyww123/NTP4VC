theory memb_free_Why3_ide_VCmemb_free_alloc_found_post_3_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal17:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (1 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a_1 (3 :: int) in l__memb_index t_3 t_1 a_1 (l__memb_ptr t_3 t_1 a_1 i) = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> i \<longrightarrow> i \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_3 t_1 a_1 \<longrightarrow> p__memb_has t_3 t_1 a_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p__memb_allocated t_3 t_2 t_1 a_1 a \<longrightarrow> \<not>(\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>shift (t_3 a_3) (i_1 * t_1 (shift a_1 (0 :: int))) = a)"
  sorry
end
