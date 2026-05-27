theory parse_ext_AKI_Why3_ide_VCparse_ext_AKI_call_parse_GeneralNames_pre_part1_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_3; x_2 :: int = i_1 + i_2 + i_3; a_3 :: addr = shift a_1 x_2; x_3 :: int = i_1 + i_2; x_4 :: int = to_sint32 x_3; x_5 :: int = i_3 + x_4; x_7 :: int = i - i_3; x_8 :: int = i - i_1 - i_2 - i_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = i \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_1 + i_3 \<le> i \<longrightarrow> i_2 + i_3 \<le> i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_2 < i \<longrightarrow> x_5 \<le> i \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> x_5 \<le> (2147483648 :: int) + i \<longrightarrow> i \<le> (65535 :: int) + i_3 + x_4 \<longrightarrow> i \<le> (2147483647 :: int) + i_3 + x_4 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> valid_rw t a (15 :: int) \<longrightarrow> is_uint16 x_7 \<longrightarrow> is_uint16 x_8 \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i) \<longrightarrow> (i_3 < i \<longrightarrow> valid_rd t a_2 x_7) \<longrightarrow> valid_rd t a_3 x_8"
  sorry
end
