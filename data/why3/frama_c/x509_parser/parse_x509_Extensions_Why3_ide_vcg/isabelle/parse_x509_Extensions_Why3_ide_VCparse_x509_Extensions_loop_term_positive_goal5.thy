theory parse_x509_Extensions_Why3_ide_VCparse_x509_Extensions_loop_term_positive_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; x_3 :: int = i_2 + i_3 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> x_3 \<le> i \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> (28 :: int) \<longrightarrow> i_1 \<le> (65534 :: int) \<longrightarrow> i_1 \<le> (2147483646 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (15 :: int) \<longrightarrow> separated a (1 :: int) a_1 (15 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i) \<longrightarrow> i_1 \<le> (29 :: int)"
  sorry
end
