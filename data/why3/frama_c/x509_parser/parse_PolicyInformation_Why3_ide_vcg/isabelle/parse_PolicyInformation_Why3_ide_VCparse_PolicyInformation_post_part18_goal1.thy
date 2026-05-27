theory parse_PolicyInformation_Why3_ide_VCparse_PolicyInformation_post_part18_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = i - i_1; a_2 :: addr = shift a_1 x_2 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i \<le> i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i \<le> i_1 + i_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (3 :: int) \<le> i_1 \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 x_2 \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_2 i_1) \<longrightarrow> (2 :: int) \<le> i"
  sorry
end
