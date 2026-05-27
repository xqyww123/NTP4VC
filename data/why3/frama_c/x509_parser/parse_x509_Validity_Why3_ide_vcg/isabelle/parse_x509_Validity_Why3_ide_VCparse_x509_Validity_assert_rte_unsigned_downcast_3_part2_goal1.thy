theory parse_x509_Validity_Why3_ide_VCparse_x509_Validity_assert_rte_unsigned_downcast_3_part2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_4; a_3 :: addr = shift a_1 (i_4 + i_5 - i_2); x_3 :: int = i_4 + i_5 in \<not>i_1 = i \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>i_5 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> i \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> i_5 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> x_3 \<le> i_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> (65535 :: int) \<longrightarrow> i_2 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 (i_5 - i_2) \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_3) \<longrightarrow> ((0 :: int) < i_5 \<longrightarrow> valid_rd t a_2 i_5) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t a_3 i_2) \<longrightarrow> x_3 \<le> (65535 :: int)"
  sorry
end
