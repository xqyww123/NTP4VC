theory parse_x509_Extension_Why3_ide_VCparse_x509_Extension_post_part137_goal27
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal27:
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_4; x_1 :: int = base a_3; x_2 :: int = i_5 + i_6; x_3 :: int = i_2 + i_5 + i_6; a_5 :: addr = shift___anonstruct__ext_oid_14 (Mk_addr (-(8682 :: int)) (0 :: int)) i_4; a_6 :: addr = shift a_4 (i - i_6); a_7 :: addr = shift a_4 (i - i_5 - i_6); x_6 :: int = i - i_2 - i_5 - i_6; a_8 :: addr = shift a_4 x_6; a_9 :: addr = shift a_1 (0 :: int); a_10 :: addr = shift a_5 (2 :: int); x_7 :: int = i_2 + i_3 + i_5 + i_6 in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>i_6 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_4 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_6 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_8 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> havoc t_1 t_2 a_9 (29 :: int) a_10 = Mk_addr (8636 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 < (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> x_3 \<le> i_3 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> i \<le> x_7 \<longrightarrow> -(2147483648 :: int) \<le> i \<longrightarrow> -(2147483648 :: int) \<le> i_6 \<longrightarrow> (2 :: int) \<le> i_5 \<longrightarrow> (3 :: int) \<le> i_2 \<longrightarrow> i_4 \<le> (28 :: int) \<longrightarrow> i \<le> (65535 :: int) \<longrightarrow> i_6 \<le> (65535 :: int) \<longrightarrow> i \<le> (2147483647 :: int) \<longrightarrow> i_6 \<le> (2147483647 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (65535 :: int) \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> (2 :: int) + i_2 + i_5 + i_6 \<le> i \<longrightarrow> x_7 \<le> (65535 :: int) + i \<longrightarrow> x_7 \<le> (2147483647 :: int) + i \<longrightarrow> i \<le> (2147483648 :: int) + i_2 + i_3 + i_5 + i_6 \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_2 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_5 \<longrightarrow> is_uint16 i_6 \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_3 (15 :: int) \<longrightarrow> is_uint16 x_2 \<longrightarrow> is_uint16 x_3 \<longrightarrow> valid_rw t a_9 (29 :: int) \<longrightarrow> is_uint16 x_6 \<longrightarrow> valid_rd t a_10 (1 :: int) \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t (shift a_4 (0 :: int)) i_3) \<longrightarrow> ((0 :: int) < i_6 \<longrightarrow> valid_rd t a_6 i_6) \<longrightarrow> ((0 :: int) < x_2 \<longrightarrow> valid_rd t a_7 x_2) \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> valid_rd t a_8 i_2) \<longrightarrow> ((0 :: int) < x_3 \<longrightarrow> valid_rd t a_8 x_3) \<longrightarrow> (0 :: int) < i"
  sorry
end
