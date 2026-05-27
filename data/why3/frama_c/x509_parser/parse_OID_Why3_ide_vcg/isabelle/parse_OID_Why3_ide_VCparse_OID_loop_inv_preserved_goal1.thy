theory parse_OID_Why3_ide_VCparse_OID_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = i - i_1 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) < i_5 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> i_5 \<le> i_3 \<longrightarrow> i_4 + i_5 \<le> i_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> (20 :: int) \<longrightarrow> i_2 \<le> (65534 :: int) \<longrightarrow> i_2 \<le> (2147483646 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_1 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> (2147483648 :: int) + i \<longrightarrow> i_3 \<le> (65535 :: int) + i_4 \<longrightarrow> i_3 \<le> (2147483647 :: int) + i_4 \<longrightarrow> i_4 \<le> (2147483648 :: int) + i_3 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 x_2 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_3) \<longrightarrow> valid_rd t (shift a_2 i_1) x_2"
  sorry
end
