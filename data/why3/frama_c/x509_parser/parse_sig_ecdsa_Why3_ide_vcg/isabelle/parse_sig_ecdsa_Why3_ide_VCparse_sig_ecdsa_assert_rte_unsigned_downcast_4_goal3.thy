theory parse_sig_ecdsa_Why3_ide_VCparse_sig_ecdsa_assert_rte_unsigned_downcast_4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal3:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_6 :: "int"
  fixes i_8 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  fixes i_7 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = i_2 + i_3 + i_6; a_2 :: addr = shift a_1 i_8; a_3 :: addr = shift a_1 ((1 :: int) + i_8); a_4 :: addr = shift a_1 ((1 :: int) + i_2 + i_8); a_5 :: addr = shift a_1 ((1 :: int) + i_2 + i_3 + i_6 + i_8); x_3 :: int = i + i_8; x_4 :: int = i_3 + i_6; x_5 :: int = to_sint32 x_4; x_6 :: int = i_2 + x_5; x_7 :: int = (2147483648 :: int) + i; x_9 :: int = i - i_2; x_10 :: int = i - i_2 - i_3 - i_6 in \<not>i = -(1 :: int) \<longrightarrow> \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = i \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < i_1 \<longrightarrow> i_2 \<le> i \<longrightarrow> i_5 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_8 \<le> i_1 \<longrightarrow> i_2 + i_3 \<le> i \<longrightarrow> i_2 + i_5 \<le> i \<longrightarrow> i_2 + i_6 \<le> i \<longrightarrow> x_3 < i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_2 \<le> i \<longrightarrow> i_2 + i_3 + i_4 + i_6 \<le> i \<longrightarrow> i_2 + i_3 + i_6 + i_7 \<le> i \<longrightarrow> i_2 + i_3 + i_4 + i_6 + i_7 \<le> i \<longrightarrow> x_6 \<le> i \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> (2 :: int) \<le> i_8 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> -(2147483649 :: int) \<le> x_3 \<longrightarrow> -(2147483648 :: int) \<le> x_4 \<longrightarrow> -(1 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65534 :: int) \<longrightarrow> x_3 \<le> (2147483646 :: int) \<longrightarrow> x_4 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_2 \<longrightarrow> i \<le> (2147483647 :: int) + i_2 \<longrightarrow> i_2 \<le> x_7 \<longrightarrow> x_6 \<le> x_7 \<longrightarrow> i \<le> (65535 :: int) + i_2 + x_5 \<longrightarrow> i \<le> (2147483647 :: int) + i_2 + x_5 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_uint16 i_6 \<longrightarrow> is_uint16 i_7 \<longrightarrow> is_uint16 i_8 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 ((1 :: int) + i) \<longrightarrow> is_uint16 x_9 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> is_uint16 x_10 \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> (i_2 < i \<longrightarrow> valid_rd t a_4 x_9) \<longrightarrow> (x_2 < i \<longrightarrow> valid_rd t a_5 x_10) \<longrightarrow> i_2 + i_3 + i_6 + to_sint32 (i_4 + i_7) \<le> i"
  sorry
end
