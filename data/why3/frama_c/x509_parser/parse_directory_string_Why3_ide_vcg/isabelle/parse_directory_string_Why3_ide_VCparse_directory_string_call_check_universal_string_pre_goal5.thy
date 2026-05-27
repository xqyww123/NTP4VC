theory parse_directory_string_Why3_ide_VCparse_directory_string_call_check_universal_string_pre_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal5:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a (1 :: int); x :: int = t_1 a_3; x_1 :: int = (2 :: int) + x in \<not>Mk_addr (0 :: int) (0 :: int) = a \<longrightarrow> \<not>a_1 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_2 = (28 :: int) \<longrightarrow> \<not>x = -(2 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> x \<le> i \<longrightarrow> i_1 \<le> x \<longrightarrow> -(2147483648 :: int) \<le> x \<longrightarrow> -(2 :: int) \<le> x \<longrightarrow> x \<le> (65535 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint16 x \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> is_uint16 x_1 \<longrightarrow> valid_rd t a_2 x_1 \<longrightarrow> valid_rd t a_1 x"
  sorry
end
