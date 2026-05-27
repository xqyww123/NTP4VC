theory get_length_Why3_ide_VCget_length_post_2_part12_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = base a_2; a_3 :: addr = shift a_1 (0 :: int); x_3 :: int = t_1 a_3; a_4 :: addr = shift a_1 (1 :: int); x_4 :: int = t_1 a_4; x_5 :: int = (256 :: int) * x_4; a_5 :: addr = shift a_1 (2 :: int); x_6 :: int = t_1 a_5; x_7 :: int = x_6 + to_sint32 x_5; x_8 :: int = x_6 + x_5 in \<not>i = (0 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> \<not>x_3 = (128 :: int) \<longrightarrow> land (127 :: int) x_3 = (2 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_7 \<longrightarrow> -(2147483645 :: int) \<le> i \<longrightarrow> (3 :: int) \<le> i \<longrightarrow> i \<le> (2147483650 :: int) \<longrightarrow> -(8388608 :: int) \<le> x_4 \<longrightarrow> x_4 \<le> (8388607 :: int) \<longrightarrow> (256 :: int) \<le> x_8 \<longrightarrow> (3 :: int) + x_6 + x_5 \<le> i \<longrightarrow> -(2147483648 :: int) \<le> x_7 \<longrightarrow> x_7 \<le> (65535 :: int) \<longrightarrow> x_7 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_4 \<longrightarrow> is_uint8 x_6 \<longrightarrow> bit_test x_3 (7 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> is_uint16 x_8 \<longrightarrow> is_uint16 ((t_1(a_2 := x_8, a := 3 :: int)) a) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> x_8 \<le> i"
  sorry
end
