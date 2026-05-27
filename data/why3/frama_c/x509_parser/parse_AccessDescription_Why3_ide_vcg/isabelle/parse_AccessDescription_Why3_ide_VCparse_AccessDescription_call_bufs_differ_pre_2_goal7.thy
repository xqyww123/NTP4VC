theory parse_AccessDescription_Why3_ide_VCparse_AccessDescription_call_bufs_differ_pre_2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_1; x_2 :: int = i_1 + i_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> x_2 \<le> i \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> (10 :: int) \<le> i_2 \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (65535 :: int) \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_1 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> (2147483648 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t a_2 i_2) \<longrightarrow> valid_rd t a_2 (10 :: int)"
  sorry
end
