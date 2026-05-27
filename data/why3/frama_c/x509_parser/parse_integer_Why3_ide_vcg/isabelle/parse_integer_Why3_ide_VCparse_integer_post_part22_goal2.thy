theory parse_integer_Why3_ide_VCparse_integer_post_part22_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; a_2 :: addr = shift a_1 i_1; x_2 :: int = t_1 a_2; x_3 :: int = i_1 + i_2 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> \<not>x_2 = (255 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> x_3 \<le> i \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> (2 :: int) \<le> i_2 \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint8 x_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i) \<longrightarrow> (3 :: int) \<le> x_3"
  sorry
end
