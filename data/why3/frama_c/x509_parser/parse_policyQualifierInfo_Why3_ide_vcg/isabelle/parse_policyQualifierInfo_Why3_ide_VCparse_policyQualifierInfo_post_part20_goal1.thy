theory parse_policyQualifierInfo_Why3_ide_VCparse_policyQualifierInfo_post_part20_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_2; a_3 :: addr = shift a_1 ((10 :: int) + i_2); x_2 :: int = i + i_2; x_3 :: int = i - (10 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i = (10 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> x_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483638 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (10 :: int) \<le> i \<longrightarrow> i \<le> (65545 :: int) \<longrightarrow> i \<le> (2147483657 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (65535 :: int) \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> (10 :: int) + i_3 \<le> i \<longrightarrow> i \<le> (65545 :: int) + i_3 \<longrightarrow> i \<le> (2147483657 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483638 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint16 x_2 \<longrightarrow> valid_rd t a_2 (10 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_2 i) \<longrightarrow> ((11 :: int) \<le> i \<longrightarrow> valid_rd t a_3 x_3) \<longrightarrow> (2 :: int) \<le> x_2"
  sorry
end
