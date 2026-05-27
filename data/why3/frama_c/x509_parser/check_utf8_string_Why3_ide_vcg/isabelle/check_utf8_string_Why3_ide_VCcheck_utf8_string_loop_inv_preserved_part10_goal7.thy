theory check_utf8_string_Why3_ide_VCcheck_utf8_string_loop_inv_preserved_part10_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a_1 (1 :: int); x_1 :: int = t_1 a_3; a_4 :: addr = shift a_1 (2 :: int); x_2 :: int = t_1 a_4; a_5 :: addr = shift a_1 (3 :: int); x_3 :: int = t_1 a_5; x_4 :: int = i - (4 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>x = (240 :: int) \<longrightarrow> \<not>x = (244 :: int) \<longrightarrow> land (192 :: int) x_1 = (128 :: int) \<longrightarrow> land (192 :: int) x_2 = (128 :: int) \<longrightarrow> land (192 :: int) x_3 = (128 :: int) \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483644 :: int) \<le> i \<longrightarrow> (4 :: int) \<le> i \<longrightarrow> i \<le> (65539 :: int) \<longrightarrow> (128 :: int) \<le> x \<longrightarrow> (194 :: int) \<le> x \<longrightarrow> (224 :: int) \<le> x \<longrightarrow> (240 :: int) \<le> x \<longrightarrow> x \<le> (244 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 x_4 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 x_1 \<longrightarrow> is_uint8 x_2 \<longrightarrow> is_uint8 x_3 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> valid_rd t (shift a_1 (4 :: int)) x_4"
  sorry
end
