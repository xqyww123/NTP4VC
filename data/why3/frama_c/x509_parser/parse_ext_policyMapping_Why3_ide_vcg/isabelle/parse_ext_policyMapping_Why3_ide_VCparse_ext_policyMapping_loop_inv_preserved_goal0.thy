theory parse_ext_policyMapping_Why3_ide_VCparse_ext_policyMapping_loop_inv_preserved_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_5 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes i_3 :: "int"
  fixes i_6 :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = i_1 + i_5; x_4 :: int = i_2 - i; a_3 :: addr = shift a_2 x_4; a_4 :: addr = shift a_2 (i_2 - i_1); x_6 :: int = i - i_5; x_7 :: int = i_1 + i_5 - i in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>i_5 = (0 :: int) \<longrightarrow> \<not>i_6 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = i \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_5 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_5 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> -(2147483648 :: int) \<le> i_1 \<longrightarrow> -(2147483648 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i_1 \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> i_1 \<le> (2147483647 :: int) \<longrightarrow> i_3 \<le> (2147483647 :: int) \<longrightarrow> (3 :: int) + i_1 \<le> i \<longrightarrow> i \<le> (65535 :: int) + i_5 \<longrightarrow> i \<le> (2147483647 :: int) + i_5 \<longrightarrow> (2 :: int) + i \<le> i_2 \<longrightarrow> i_5 \<le> (2147483648 :: int) + i \<longrightarrow> (3 :: int) + i \<le> x_2 \<longrightarrow> x_2 \<le> (65535 :: int) + i \<longrightarrow> x_2 \<le> (2147483647 :: int) + i \<longrightarrow> i \<le> (2147483648 :: int) + i_1 + i_5 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_sint32 i_6 \<longrightarrow> valid_rw t a (15 :: int) \<longrightarrow> is_uint16 (i - i_1) \<longrightarrow> is_uint16 x_6 \<longrightarrow> is_uint16 x_4 \<longrightarrow> is_uint16 (i_3 - i_4) \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_2 \<longrightarrow> is_uint16 x_7 \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_3) \<longrightarrow> ((0 :: int) < i_5 \<longrightarrow> valid_rd t a_3 i_5) \<longrightarrow> (i < x_2 \<longrightarrow> valid_rd t a_4 x_7) \<longrightarrow> valid_rd t (shift a_2 (i_2 + i_5 - i)) x_6"
  sorry
end
