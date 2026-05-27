theory parse_GeneralName_Why3_ide_VCparse_GeneralName_call_get_length_pre_2_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal14:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 (1 :: int); a_4 :: addr = shift a_2 (0 :: int); x_3 :: int = i - (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>a_1 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_4 = (135 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> -(2147483647 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i \<le> (65536 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_4 i \<longrightarrow> valid_rd t a_3 x_3"
  sorry
end
