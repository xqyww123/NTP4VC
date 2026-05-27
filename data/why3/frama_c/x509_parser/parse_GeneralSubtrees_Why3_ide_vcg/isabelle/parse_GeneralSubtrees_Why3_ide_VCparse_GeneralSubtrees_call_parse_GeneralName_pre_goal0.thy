theory parse_GeneralSubtrees_Why3_ide_VCparse_GeneralSubtrees_call_parse_GeneralName_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>a_1 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i + i_2 \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1) \<longrightarrow> valid_rd t a_1 i"
  sorry
end
