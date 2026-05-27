theory parse_x509_Extensions_Why3_ide_VCparse_x509_Extensions_loop_inv_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes a_3 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "int \<Rightarrow> addr"
  fixes t_1 :: "int \<Rightarrow> addr"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; x_3 :: int = i_3 + i_5; x_4 :: int = i - i_4 in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = i \<longrightarrow> \<not>i_5 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_3 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> (0 :: int) < i_4 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> i_5 \<le> i_1 \<longrightarrow> x_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (29 :: int) \<le> i_2 \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> i \<le> (65535 :: int) + i_4 \<longrightarrow> i \<le> (2147483647 :: int) + i_4 \<longrightarrow> i_4 \<le> (2147483648 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_uint16 i_5 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (15 :: int) \<longrightarrow> separated a (1 :: int) a_1 (15 :: int) \<longrightarrow> is_uint16 x_4 \<longrightarrow> valid_rd t (shift a_3 (0 :: int)) i \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 \<le> (28 :: int) \<longrightarrow> i_6 < (0 :: int) \<or> (29 :: int) \<le> i_6 \<longrightarrow> t_2 i_6 = t_1 i_6) \<longrightarrow> valid_rd t (shift a_3 i_4) x_4"
  sorry
end
