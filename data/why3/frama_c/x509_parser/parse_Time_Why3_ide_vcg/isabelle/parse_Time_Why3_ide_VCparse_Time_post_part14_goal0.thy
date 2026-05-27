theory parse_Time_Why3_ide_VCparse_Time_post_part14_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_8 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i_6 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_8; x_1 :: int = base a; x_2 :: int = base a_1; x_3 :: int = base a_2; x_4 :: int = base a_3; x_5 :: int = base a_4; x_6 :: int = base a_5; x_7 :: int = base a_6; x_8 :: int = base a_7; a_9 :: addr = shift a_8 (0 :: int); x_9 :: int = (t_1(a_1 := 23 :: int, a_6 := 15 :: int, a := i_5, a_3 := i_4, a_7 := i_3, a_5 := i_2, a_4 := i_1, a_2 := i)) a_6 in \<not>a_1 = a \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>a_2 = a_1 \<longrightarrow> \<not>a_3 = a \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> \<not>a_4 = a \<longrightarrow> \<not>a_4 = a_1 \<longrightarrow> \<not>a_4 = a_2 \<longrightarrow> \<not>a_4 = a_3 \<longrightarrow> \<not>i_6 = (0 :: int) \<longrightarrow> \<not>a_5 = a \<longrightarrow> \<not>a_5 = a_1 \<longrightarrow> \<not>a_5 = a_2 \<longrightarrow> \<not>a_5 = a_3 \<longrightarrow> \<not>a_5 = a_4 \<longrightarrow> \<not>a_6 = a \<longrightarrow> \<not>a_6 = a_1 \<longrightarrow> \<not>a_6 = a_2 \<longrightarrow> \<not>a_6 = a_3 \<longrightarrow> \<not>a_6 = a_4 \<longrightarrow> \<not>a_6 = a_5 \<longrightarrow> \<not>a_7 = a \<longrightarrow> \<not>a_7 = a_1 \<longrightarrow> \<not>a_7 = a_2 \<longrightarrow> \<not>a_7 = a_3 \<longrightarrow> \<not>a_7 = a_4 \<longrightarrow> \<not>a_7 = a_5 \<longrightarrow> \<not>a_7 = a_6 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_8 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>x = x_3 \<longrightarrow> \<not>x = x_4 \<longrightarrow> \<not>x = x_5 \<longrightarrow> \<not>x = x_6 \<longrightarrow> \<not>x = x_7 \<longrightarrow> \<not>x = x_8 \<longrightarrow> t_1 a_9 = (23 :: int) \<longrightarrow> (0 :: int) \<le> i_6 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x_3 \<le> (0 :: int) \<longrightarrow> region x_4 \<le> (0 :: int) \<longrightarrow> region x_5 \<le> (0 :: int) \<longrightarrow> region x_6 \<le> (0 :: int) \<longrightarrow> region x_7 \<le> (0 :: int) \<longrightarrow> region x_8 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_6 \<longrightarrow> (15 :: int) \<le> i_6 \<longrightarrow> linked t \<longrightarrow> is_uint16 i_6 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> valid_rw t a_6 (1 :: int) \<longrightarrow> valid_rw t a_7 (1 :: int) \<longrightarrow> valid_rd t a_9 (1 :: int) \<longrightarrow> separated a (1 :: int) a_9 i_6 \<longrightarrow> separated a_2 (1 :: int) a_9 i_6 \<longrightarrow> separated a_3 (1 :: int) a_9 i_6 \<longrightarrow> separated a_4 (1 :: int) a_9 i_6 \<longrightarrow> separated a_5 (1 :: int) a_9 i_6 \<longrightarrow> separated a_6 (1 :: int) a_9 i_6 \<longrightarrow> separated a_7 (1 :: int) a_9 i_6 \<longrightarrow> is_uint16 x_9 \<longrightarrow> ((0 :: int) < i_6 \<longrightarrow> valid_rd t a_9 i_6) \<longrightarrow> x_9 \<le> i_6"
  sorry
end
