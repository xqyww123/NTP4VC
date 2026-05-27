theory parse_GeneralSubtrees_Why3_ide_VCparse_GeneralSubtrees_call_parse_id_len_pre_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2; a_2 :: addr = shift a (i_2 + i_3); x :: int = i_4 - i_3 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>a_1 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_4 \<le> i_1 \<longrightarrow> i_3 < i_4 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_2 + i_4 \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (1 :: int) \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_4 \<longrightarrow> i_4 \<le> (65535 :: int) + i_3 \<longrightarrow> i_4 \<le> (2147483647 :: int) + i_3 \<longrightarrow> linked t \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint16 x \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t a_1 i_4) \<longrightarrow> valid_rd t a_2 x"
  sorry
end
