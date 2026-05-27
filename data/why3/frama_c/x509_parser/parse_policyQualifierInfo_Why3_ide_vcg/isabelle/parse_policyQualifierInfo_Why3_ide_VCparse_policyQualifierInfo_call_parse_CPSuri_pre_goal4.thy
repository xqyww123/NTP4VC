theory parse_policyQualifierInfo_Why3_ide_VCparse_policyQualifierInfo_call_parse_CPSuri_pre_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_2; a_3 :: addr = shift a_1 ((10 :: int) + i_2); x_2 :: int = i - (10 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i + i_2 \<le> i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483638 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (10 :: int) \<le> i \<longrightarrow> (11 :: int) \<le> i \<longrightarrow> i \<le> (65545 :: int) \<longrightarrow> i \<le> (2147483657 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 x_2 \<longrightarrow> valid_rd t a_2 (10 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_2 i) \<longrightarrow> valid_rd t a_3 x_2"
  sorry
end
