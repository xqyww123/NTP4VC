theory get_identifier_Why3_ide_VCget_identifier_post_2_part4_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_4; x_1 :: int = base a; x_2 :: int = base a_1; x_3 :: int = base a_2; x_4 :: int = base a_3; a_5 :: addr = shift a_4 (1 :: int); a_6 :: addr = shift a_4 (0 :: int); x_5 :: int = t_1 a_6; x_6 :: int = lsr x_5 (5 :: int); x_7 :: int = (1 :: int) + i; x_8 :: int = land (3 :: int) (lsr x_5 (6 :: int)); x_9 :: int = (t_1(a_2 := x_7, a := i_1, a_1 := land (1 :: int) x_6, a_3 := x_8)) a_1 in \<not>a_1 = a \<longrightarrow> \<not>i_2 = (0 :: int) \<longrightarrow> \<not>i_2 = (1 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>a_2 = a_1 \<longrightarrow> \<not>a_3 = a \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_4 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>x = x_3 \<longrightarrow> \<not>x = x_4 \<longrightarrow> \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> land (31 :: int) x_5 = (31 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i < i_2 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x_3 \<le> (0 :: int) \<longrightarrow> region x_4 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_5 \<longrightarrow> (0 :: int) \<le> land (1 :: int) (to_sint32 x_6) \<longrightarrow> -(2147483649 :: int) \<le> i \<longrightarrow> -(2147483647 :: int) \<le> i_2 \<longrightarrow> i \<le> (65534 :: int) \<longrightarrow> i_2 \<le> (65536 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> i_2 \<le> (2147483648 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> is_uint16 x_7 \<longrightarrow> is_uint8 x_5 \<longrightarrow> valid_rd t a_6 (1 :: int) \<longrightarrow> valid_rd t a_6 i_2 \<longrightarrow> valid_rd t a_5 (i_2 - (1 :: int)) \<longrightarrow> is_uint32 x_8 \<longrightarrow> is_uint8 x_9 \<longrightarrow> x_8 = (0 :: int) \<or> x_8 = (1 :: int) \<or> x_8 = (2 :: int) \<or> x_8 = (3 :: int) \<longrightarrow> x_9 \<le> (1 :: int)"
  sorry
end
