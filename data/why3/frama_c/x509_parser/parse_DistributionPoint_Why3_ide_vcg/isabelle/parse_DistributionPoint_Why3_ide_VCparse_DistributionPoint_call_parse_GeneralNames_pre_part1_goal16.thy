theory parse_DistributionPoint_Why3_ide_VCparse_DistributionPoint_call_parse_GeneralNames_pre_part1_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal16:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_7 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 i_3; x_3 :: int = i + i_5; a_4 :: addr = shift a_2 (i_3 + i_5); a_5 :: addr = shift a_2 (i_3 + i_5 + i_6); a_6 :: addr = shift a_2 (i_1 + i_3 + i_5 + i_6); x_4 :: int = i_1 + i_6; x_5 :: int = i + i_3 + i_5; x_6 :: int = (2147483648 :: int) + i; x_8 :: int = i - i_6; x_9 :: int = i - i_1 - i_6 in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_6 = (0 :: int) \<longrightarrow> \<not>i_6 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_4 = (160 :: int) \<longrightarrow> \<not>a_6 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_6 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> i_4 + i_6 \<le> i \<longrightarrow> i_6 + i_7 \<le> i \<longrightarrow> x_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> i_6 \<le> x_3 \<longrightarrow> x_4 < i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> i_4 + i_6 + i_7 \<le> i \<longrightarrow> x_5 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_5 \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> (2 :: int) \<le> i_5 \<longrightarrow> (2 :: int) \<le> i_6 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_6 \<longrightarrow> i \<le> (2147483647 :: int) + i_6 \<longrightarrow> i_6 \<le> x_6 \<longrightarrow> x_4 \<le> x_6 \<longrightarrow> -(2147483648 :: int) \<le> x_5 \<longrightarrow> x_5 \<le> (65535 :: int) \<longrightarrow> x_5 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_1 + i_6 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 + i_6 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_uint16 i_6 \<longrightarrow> is_uint16 i_7 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (15 :: int) \<longrightarrow> separated a (1 :: int) a_1 (15 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint16 x_8 \<longrightarrow> is_uint16 x_9 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < x_3 \<longrightarrow> valid_rd t a_3 x_3) \<longrightarrow> ((0 :: int) < i_6 \<longrightarrow> valid_rd t a_4 i_6) \<longrightarrow> (i_6 < i \<longrightarrow> valid_rd t a_5 x_8) \<longrightarrow> valid_rd t a_6 x_9"
  sorry
end
