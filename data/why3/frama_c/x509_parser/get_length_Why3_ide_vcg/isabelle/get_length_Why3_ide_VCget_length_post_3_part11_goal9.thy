theory get_length_Why3_ide_VCget_length_post_3_part11_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = base a_2; a_3 :: addr = shift a_1 (0 :: int); x_3 :: int = t_1 a_3; a_4 :: addr = shift a_1 (1 :: int); x_4 :: int = t_1 a_4; x_5 :: int = (t_1(a_2 := x_4, a := 2 :: int)) a in \<not>i = (0 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> \<not>x_3 = (128 :: int) \<longrightarrow> land (127 :: int) x_3 = (1 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> -(2147483646 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> i \<le> (2147483649 :: int) \<longrightarrow> (128 :: int) \<le> x_4 \<longrightarrow> (2 :: int) + x_4 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint8 x_4 \<longrightarrow> is_uint16 x_4 \<longrightarrow> bit_test x_3 (7 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> is_uint16 x_5 \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> x_4 + x_5 \<le> i"
  sorry
end
