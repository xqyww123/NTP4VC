theory parse_GeneralName_Why3_ide_VCparse_GeneralName_post_part26_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 (1 :: int); x_3 :: int = i + i_2; a_4 :: addr = shift a_2 (0 :: int); a_5 :: addr = shift a_2 ((1 :: int) + i_2); x_4 :: int = i_1 + i_2; x_5 :: int = to_sint32 x_4; x_6 :: int = (1 :: int) + i + i_2; x_7 :: int = (t_1(a := 0 :: int, a_1 := (1 :: int) + i_1 + i_2)) a_1 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>a_1 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x_3 = -(1 :: int) \<longrightarrow> t_1 a_4 = (129 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) < x_3 \<longrightarrow> i_1 \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> -(2147483648 :: int) \<le> x_4 \<longrightarrow> -(1 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_4 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_1 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> (2147483648 :: int) + i \<longrightarrow> -(1 :: int) \<le> x_5 \<longrightarrow> x_5 \<le> (65534 :: int) \<longrightarrow> x_5 \<le> (2147483646 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint16 x_6 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_3 x_3 \<longrightarrow> valid_rd t a_4 x_6 \<longrightarrow> is_uint16 x_7 \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_5 i_1) \<longrightarrow> (2 :: int) \<le> x_7"
  sorry
end
