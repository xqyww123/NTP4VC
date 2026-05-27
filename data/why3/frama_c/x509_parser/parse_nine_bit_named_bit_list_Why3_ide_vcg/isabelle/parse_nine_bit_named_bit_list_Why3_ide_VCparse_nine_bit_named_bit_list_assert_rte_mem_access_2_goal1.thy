theory parse_nine_bit_named_bit_list_Why3_ide_VCparse_nine_bit_named_bit_list_assert_rte_mem_access_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cbits_Cbits"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 (0 :: int); x_2 :: int = t_1 a_2 in \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> land (248 :: int) x_2 = (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint8 x_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 (2 :: int) \<longrightarrow> valid_rd t (shift a_1 (1 :: int)) (1 :: int)"
  sorry
end
