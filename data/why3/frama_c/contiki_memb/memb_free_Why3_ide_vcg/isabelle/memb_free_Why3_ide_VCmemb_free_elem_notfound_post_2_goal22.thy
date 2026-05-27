theory memb_free_Why3_ide_VCmemb_free_elem_notfound_post_2_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal22:
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = l__memb_ptr t_3 t_1 a i; a_2 :: addr = shift a (1 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a (2 :: int); a_4 :: addr = shift a (3 :: int); a_5 :: addr = shift (t_3 a_3) i in l__memb_index t_3 t_1 a a_1 = i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> is_sint8 (t_2 a_5) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> \<not>p__memb_has t_3 t_1 a a_1 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> \<not>shift (t_3 a_4) (i_1 * t_1 (shift a (0 :: int))) = a_1) \<longrightarrow> l__memb_numfree t_3 (t_2(a_5 := 0 :: int)) t_1 a = l__memb_numfree t_3 t_2 t_1 a"
  sorry
end
