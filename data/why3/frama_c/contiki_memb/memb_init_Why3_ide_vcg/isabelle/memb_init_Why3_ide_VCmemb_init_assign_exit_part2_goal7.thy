theory memb_init_Why3_ide_VCmemb_init_assign_exit_part2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint" "frama_c_contiki_memb_lib.Axiomatic12_Axiomatic12" "frama_c_contiki_memb_lib.A_MemSet_A_MemSet"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (0 :: int); x_1 :: int = t_1 a_2; x_2 :: int = x * x_1; a_3 :: addr = shift a (2 :: int); a_4 :: addr = shift a (3 :: int); a_5 :: addr = t_4 a_3; a_6 :: addr = t_4 a_4; a_7 :: addr = shift a_6 (0 :: int); x_3 :: int = to_uint32 x_2; a_8 :: addr = shift a_5 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_4 t_1 a \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p_valid_or_empty t a_5 x \<longrightarrow> \<not>invalid t a_7 x_3 \<longrightarrow> p_valid_or_empty t a_6 x_3 \<longrightarrow> l_memset (havoc t_2 t_3 a_8 x) a_5 (0 :: int) x = True \<longrightarrow> included a_7 x_3 a_8 x \<or> ((0 :: int) < x_3 \<longrightarrow> x_3 \<le> x_2)"
  sorry
end
