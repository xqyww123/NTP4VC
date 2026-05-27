theory parse_GeneralName_Why3_ide_VCparse_GeneralName_post_part34_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 (1 :: int); a_4 :: addr = shift a_2 (0 :: int); x_3 :: int = (2147483648 :: int) + i_1; x_5 :: int = to_sint32 (i + i_2 - (1 :: int) - i_1); x_6 :: int = i - (1 :: int); x_7 :: int = (t_1(a := if i_2 = (0 :: int) then 1 :: int else (0 :: int), a_1 := i + i_2 - i_1)) a_1 in \<not>i = (0 :: int) \<longrightarrow> \<not>i = (1 :: int) \<longrightarrow> \<not>a_1 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_4 = (135 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_1 \<longrightarrow> -(2147483647 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i_1 \<le> (65535 :: int) \<longrightarrow> i \<le> (65536 :: int) \<longrightarrow> i_1 \<le> (2147483647 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> i_1 \<le> (65535 :: int) + i_2 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_2 \<longrightarrow> i_2 \<le> x_3 \<longrightarrow> i + i_2 \<le> x_3 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i + i_2 \<longrightarrow> -(1 :: int) \<le> x_5 \<longrightarrow> x_5 \<le> (65534 :: int) \<longrightarrow> x_5 \<le> (2147483646 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_uint16 x_6 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_4 i \<longrightarrow> valid_rd t a_3 x_6 \<longrightarrow> is_uint16 (i - (1 :: int) - i_1) \<longrightarrow> is_uint16 x_7 \<longrightarrow> (2 :: int) \<le> x_7"
  sorry
end
