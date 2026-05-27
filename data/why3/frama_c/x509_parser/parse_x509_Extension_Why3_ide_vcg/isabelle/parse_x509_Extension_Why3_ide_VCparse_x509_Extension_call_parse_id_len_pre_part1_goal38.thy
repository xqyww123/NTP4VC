theory parse_x509_Extension_Why3_ide_VCparse_x509_Extension_call_parse_id_len_pre_part1_goal38
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "frama_c_x509_parser_lib.Globals_Globals" "Why3STD.Cint_Cint"
begin
theorem goal38:
  fixes a_3 :: "addr"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_4 :: addr = shift a_3 i_3; x :: int = i + i_4; a_5 :: addr = shift a_3 (i + i_3); a_6 :: addr = shift a_3 ((3 :: int) + i + i_3); a_7 :: addr = shift a_3 ((2 :: int) + i + i_3); x_1 :: int = t_1 a_7; x_2 :: int = i + i_3 + i_4; x_3 :: int = i_4 - (3 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>i_1 = (0 :: int) \<longrightarrow> \<not>i_4 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_3 \<longrightarrow> \<not>a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>shift___anonstruct__ext_oid_14 (Mk_addr (-(8682 :: int)) (0 :: int)) i_2 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>a_6 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> x \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> -(2147483648 :: int) \<le> i_4 \<longrightarrow> -(2147483645 :: int) \<le> i_4 \<longrightarrow> (2 :: int) \<le> i_3 \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> (3 :: int) \<le> i_4 \<longrightarrow> (4 :: int) \<le> i_4 \<longrightarrow> i_2 \<le> (28 :: int) \<longrightarrow> i_4 \<le> (65535 :: int) \<longrightarrow> i_4 \<le> (65538 :: int) \<longrightarrow> i_4 \<le> (2147483647 :: int) \<longrightarrow> i_4 \<le> (2147483650 :: int) \<longrightarrow> i_1 \<le> (65535 :: int) + i_3 \<longrightarrow> i_1 \<le> (2147483647 :: int) + i_3 \<longrightarrow> i_3 \<le> (2147483648 :: int) + i_1 \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (65535 :: int) \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (15 :: int) \<longrightarrow> is_uint16 x_3 \<longrightarrow> is_uint16 x \<longrightarrow> valid_rw t (shift a (0 :: int)) (29 :: int) \<longrightarrow> is_uint8 x_1 \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_3 (0 :: int)) i_1) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_4 i) \<longrightarrow> ((0 :: int) < x \<longrightarrow> valid_rd t a_4 x) \<longrightarrow> ((0 :: int) < i_4 \<longrightarrow> valid_rd t a_5 i_4) \<longrightarrow> valid_rd t a_6 x_3"
  sorry
end
