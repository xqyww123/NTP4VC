theory parse_x509_AlgorithmIdentifier_Why3_ide_VCparse_x509_AlgorithmIdentifier_post_part11_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_x509_parser_lib.Globals_Globals"
begin
theorem goal2:
  fixes t_1 :: "int \<Rightarrow> addr"
  fixes i_4 :: "int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = t_1 i_4; x :: int = base a_2; x_1 :: int = base a; a_5 :: addr = shift a_2 i_5; x_2 :: int = i + i_1; a_6 :: addr = shift a_4 (7 :: int); x_3 :: int = i + i_1 + i_5; a_7 :: addr = shift a_2 (i_1 + i_5) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>a_2 = a_1 \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> t_2 a_6 = Mk_addr (8420 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_5 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> x_2 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_3 \<le> i_2 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_5 \<longrightarrow> (3 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> (5 :: int) \<longrightarrow> i_4 \<le> (26 :: int) \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_5 \<longrightarrow> valid_rw t a (4 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> separated a (4 :: int) a_1 (1 :: int) \<longrightarrow> separated a_2 (1 :: int) a (4 :: int) \<longrightarrow> separated a_3 (1 :: int) a (4 :: int) \<longrightarrow> is_uint16 x_2 \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_2) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t a_5 i_1) \<longrightarrow> ((0 :: int) < x_2 \<longrightarrow> valid_rd t a_5 x_2) \<longrightarrow> (\<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> valid_rd t a_7 i) \<longrightarrow> (\<exists>(i_6 :: int). a_4 = t_1 i_6 \<and> is_uint8 i_6)"
  sorry
end
