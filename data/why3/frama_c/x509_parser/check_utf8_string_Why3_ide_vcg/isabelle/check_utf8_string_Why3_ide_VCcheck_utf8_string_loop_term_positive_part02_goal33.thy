theory check_utf8_string_Why3_ide_VCcheck_utf8_string_loop_term_positive_part02_goal33
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits"
begin
theorem goal33:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (1 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a_1 (0 :: int); x_1 :: int = t_1 a_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> land (192 :: int) x = (128 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483646 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i \<le> (65537 :: int) \<longrightarrow> (128 :: int) \<le> x_1 \<longrightarrow> (194 :: int) \<le> x_1 \<longrightarrow> x_1 \<le> (223 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> (0 :: int) \<le> i"
  sorry
end
