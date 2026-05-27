theory parse_AccessDescription_Why3_ide_VCparse_AccessDescription_assert_rte_unsigned_downcast_4_pa____2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_3 :: int = i_2 - i_1; a_2 :: addr = shift a_1 x_3; a_3 :: addr = shift a_1 ((10 :: int) + i_2 - i_1); x_4 :: int = i_2 + i_3; x_5 :: int = (10 :: int) + i_5; x_6 :: int = i_3 - (10 :: int) in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>i_3 = (10 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_1 \<le> x_4 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_1 \<longrightarrow> -(2147483638 :: int) \<le> i_1 \<longrightarrow> -(2147483638 :: int) \<le> i_3 \<longrightarrow> i \<le> (1 :: int) \<longrightarrow> (2 :: int) \<le> i_5 \<longrightarrow> (10 :: int) \<le> i_1 \<longrightarrow> (10 :: int) \<le> i_3 \<longrightarrow> i_1 \<le> (65535 :: int) \<longrightarrow> i_1 \<le> (65545 :: int) \<longrightarrow> i_3 \<le> (65545 :: int) \<longrightarrow> i_1 \<le> (2147483647 :: int) \<longrightarrow> i_1 \<le> (2147483657 :: int) \<longrightarrow> i_3 \<le> (2147483657 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i_2 \<longrightarrow> x_5 \<le> i_3 \<longrightarrow> x_4 \<le> (65535 :: int) + i_1 \<longrightarrow> x_4 \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> (2147483648 :: int) + i_2 + i_3 \<longrightarrow> linked t \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint16 (i_1 - (10 :: int)) \<longrightarrow> is_uint16 x_6 \<longrightarrow> is_uint16 x_3 \<longrightarrow> valid_rd t a_2 (10 :: int) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t a_2 i_3) \<longrightarrow> ((11 :: int) \<le> i_3 \<longrightarrow> valid_rd t a_3 x_6) \<longrightarrow> x_5 \<le> i_1"
  sorry
end
