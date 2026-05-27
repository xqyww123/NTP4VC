theory parse_ext_IAN_Why3_ide_VCparse_ext_IAN_loop_term_decrease_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = i_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i_2 \<longrightarrow> i \<le> (1 :: int) \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> (2147483647 :: int) \<longrightarrow> i_1 \<le> (65535 :: int) + i_4 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_4 \<longrightarrow> i_4 \<le> (2147483648 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a (15 :: int) \<longrightarrow> is_uint16 (i_1 - i_4) \<longrightarrow> is_uint16 (i_2 - i_3) \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1 \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2) \<longrightarrow> (0 :: int) < i_4"
  sorry
end
