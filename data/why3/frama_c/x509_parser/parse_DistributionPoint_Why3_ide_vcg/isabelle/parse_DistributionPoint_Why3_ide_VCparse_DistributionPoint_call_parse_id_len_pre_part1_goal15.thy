theory parse_DistributionPoint_Why3_ide_VCparse_DistributionPoint_call_parse_id_len_pre_part1_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal15:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 i_3; a_4 :: addr = shift a_2 (i + i_3 - i_1); a_5 :: addr = shift a_2 (i + i_3 + i_4 - i_1); x_4 :: int = i + i_3; x_5 :: int = i_1 - i_4 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_4 = (160 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> x_4 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> i_1 \<le> (65535 :: int) \<longrightarrow> i_1 \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_4 \<longrightarrow> x_4 \<le> (65535 :: int) \<longrightarrow> x_4 \<le> (2147483647 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> i_1 \<le> (65535 :: int) + i_4 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_4 \<longrightarrow> i_4 \<le> (2147483648 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (15 :: int) \<longrightarrow> separated a (1 :: int) a_1 (15 :: int) \<longrightarrow> is_uint16 (i - i_1) \<longrightarrow> is_uint16 x_5 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t a_4 i_4) \<longrightarrow> valid_rd t a_5 x_5"
  sorry
end
