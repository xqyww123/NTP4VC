theory parse_AccessDescription_Why3_ide_VCparse_AccessDescription_call_parse_GeneralName_pre_part08_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_3 :: int = i_1 - i; a_2 :: addr = shift a_1 x_3; a_3 :: addr = shift a_1 ((10 :: int) + i_1 - i); x_4 :: int = i_1 + i_2; x_5 :: int = i_2 - (10 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> -(2147483638 :: int) \<le> i \<longrightarrow> -(2147483638 :: int) \<le> i_2 \<longrightarrow> (10 :: int) \<le> i \<longrightarrow> (10 :: int) \<le> i_2 \<longrightarrow> (11 :: int) \<le> i_2 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (65545 :: int) \<longrightarrow> i_2 \<le> (65545 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> i \<le> (2147483657 :: int) \<longrightarrow> i_2 \<le> (2147483657 :: int) \<longrightarrow> (2 :: int) + i \<le> i_1 \<longrightarrow> x_4 \<le> (65535 :: int) + i \<longrightarrow> x_4 \<le> (2147483647 :: int) + i \<longrightarrow> i \<le> (2147483648 :: int) + i_1 + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 x_5 \<longrightarrow> is_uint16 x_3 \<longrightarrow> valid_rd t a_2 (10 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t a_2 i_2) \<longrightarrow> valid_rd t a_3 x_5"
  sorry
end
