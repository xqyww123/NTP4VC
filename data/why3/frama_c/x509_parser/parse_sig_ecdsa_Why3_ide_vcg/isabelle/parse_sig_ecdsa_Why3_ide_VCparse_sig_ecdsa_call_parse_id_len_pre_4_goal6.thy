theory parse_sig_ecdsa_Why3_ide_VCparse_sig_ecdsa_call_parse_id_len_pre_4_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal6:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_6; a_3 :: addr = shift a_1 ((1 :: int) + i_6); a_4 :: addr = shift a_1 ((1 :: int) + i_2 + i_6); a_5 :: addr = shift a_1 ((1 :: int) + i_2 + i_3 + i_5 + i_6); x_2 :: int = i + i_6; x_3 :: int = i_3 + i_5; x_4 :: int = to_sint32 x_3; x_5 :: int = i_2 + x_4; x_6 :: int = (2147483648 :: int) + i; x_8 :: int = i - i_2; x_9 :: int = i - i_2 - i_3 - i_5 in \<not>i = -(1 :: int) \<longrightarrow> \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < i_1 \<longrightarrow> i_2 \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_6 \<le> i_1 \<longrightarrow> i_2 + i_3 \<le> i \<longrightarrow> i_2 + i_4 \<le> i \<longrightarrow> i_2 + i_5 \<le> i \<longrightarrow> x_2 < i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i_2 + i_3 + i_5 < i \<longrightarrow> x_5 \<le> i \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_6 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> -(2147483649 :: int) \<le> x_2 \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> -(1 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (65534 :: int) \<longrightarrow> x_2 \<le> (2147483646 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_2 \<longrightarrow> i \<le> (2147483647 :: int) + i_2 \<longrightarrow> i_2 \<le> x_6 \<longrightarrow> x_5 \<le> x_6 \<longrightarrow> i \<le> (65535 :: int) + i_2 + x_4 \<longrightarrow> i \<le> (2147483647 :: int) + i_2 + x_4 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_uint16 i_6 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 ((1 :: int) + i) \<longrightarrow> is_uint16 x_8 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> is_uint16 x_9 \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> (i_2 < i \<longrightarrow> valid_rd t a_4 x_8) \<longrightarrow> valid_rd t a_5 x_9"
  sorry
end
