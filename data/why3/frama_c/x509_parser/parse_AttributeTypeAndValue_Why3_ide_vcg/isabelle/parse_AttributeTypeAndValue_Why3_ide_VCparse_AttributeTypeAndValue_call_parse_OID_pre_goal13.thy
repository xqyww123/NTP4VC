theory parse_AttributeTypeAndValue_Why3_ide_VCparse_AttributeTypeAndValue_call_parse_OID_pre_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal13:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; x :: int = i_1 + i_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> x \<le> i \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> -(2147483648 :: int) \<le> x \<longrightarrow> x \<le> (65535 :: int) \<longrightarrow> x \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_1 \<longrightarrow> i \<le> (2147483647 :: int) + i_1 \<longrightarrow> i_1 \<le> (2147483648 :: int) + i \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i) \<longrightarrow> valid_rd t a_2 i_2"
  sorry
end
