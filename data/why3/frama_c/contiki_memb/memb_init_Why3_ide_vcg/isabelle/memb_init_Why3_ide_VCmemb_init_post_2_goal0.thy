theory memb_init_Why3_ide_VCmemb_init_post_2_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint" "frama_c_contiki_memb_lib.Axiomatic12_Axiomatic12" "frama_c_contiki_memb_lib.A_MemSet_A_MemSet"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (0 :: int); x_1 :: int = t_1 a_2; x_2 :: int = x * x_1; a_3 :: addr = shift a (2 :: int); a_4 :: addr = shift a (3 :: int); a_5 :: addr = t_5 a_3; a_6 :: addr = t_5 a_4; x_3 :: int = to_uint32 x_2; a_7 :: addr \<Rightarrow> int = havoc t_2 t_4 (shift a_5 (0 :: int)) x; a_8 :: addr \<Rightarrow> int = havoc t_3 a_7 (shift a_6 (0 :: int)) x_3 in region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> framed t_5 \<longrightarrow> linked t \<longrightarrow> sconst t_4 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_5 t_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p_valid_or_empty t a_5 x \<longrightarrow> p_valid_or_empty t a_6 x_3 \<longrightarrow> l_memset a_7 a_5 (0 :: int) x = True \<longrightarrow> l_memset a_8 a_6 (0 :: int) x_3 = True \<longrightarrow> p__memb_empty t_5 a_8 t_1 a"
  sorry
end
