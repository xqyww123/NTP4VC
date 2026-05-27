theory memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_2_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = t_3 a_1; a_3 :: addr = shift a_2 i; x :: int = t_2 a_3; a_4 :: addr = shift a (1 :: int); x_1 :: int = t_1 a_4; x_2 :: int = l_occ_a t_2 (0 :: int) a_2 (0 :: int) i; x_3 :: int = (1 :: int) + i in \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> i \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_2 \<le> i \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x_1 \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> is_sint8 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> x_2 \<le> x_3"
  sorry
end
