theory memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (2 :: int); a_3 :: addr = t_3 a_2; x_1 :: int = l_occ_a t_2 (0 :: int) a_3 (0 :: int) i_1; a_4 :: addr = shift a_3 i_1; x_2 :: int = t_2 a_4 in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> i_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 \<le> i_1 \<longrightarrow> i_1 \<le> (2147483646 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint16 x \<longrightarrow> is_sint32 ((1 :: int) + i_1) \<longrightarrow> p_valid_memb t t_3 t_1 a \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint8 x_2 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> is_sint32 x_1 \<longrightarrow> \<not>x_2 = (0 :: int) \<or> x_1 = i \<and> i \<le> (2147483646 :: int) \<longrightarrow> -(1 :: int) \<le> i_1"
  sorry
end
