theory bufs_differ_Why3_ide_VCbufs_differ_loop_inv_2_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Axiomatic12_Axiomatic12"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; x :: int = t_1 a_2; a_3 :: addr = shift a i_1; x_1 :: int = t_1 a_3; x_2 :: int = (1 :: int) + i_1 in x = x_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> (65534 :: int) \<longrightarrow> i_1 \<le> (2147483646 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 x_2 \<longrightarrow> p_bmatch t_1 a_1 a i_1 \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> p_bmatch t_1 a_1 a x_2"
  sorry
end
