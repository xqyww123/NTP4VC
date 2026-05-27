theory parse_UTCTime_Why3_ide_VCparse_UTCTime_loop_inv_2_preserved_part1_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_7 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_8 :: addr = shift a_7 (0 :: int); a_9 :: addr = shift a_7 (1 :: int); a_10 :: addr = shift a_7 ((2 :: int) + i_1); x :: int = t_1 a_10 in \<not>a_1 = a \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>a_2 = a_1 \<longrightarrow> \<not>a_3 = a \<longrightarrow> \<not>a_3 = a_1 \<longrightarrow> \<not>a_3 = a_2 \<longrightarrow> \<not>a_4 = a \<longrightarrow> \<not>a_4 = a_1 \<longrightarrow> \<not>a_4 = a_2 \<longrightarrow> \<not>a_4 = a_3 \<longrightarrow> \<not>a_5 = a \<longrightarrow> \<not>a_5 = a_1 \<longrightarrow> \<not>a_5 = a_2 \<longrightarrow> \<not>a_5 = a_3 \<longrightarrow> \<not>a_5 = a_4 \<longrightarrow> \<not>a_6 = a \<longrightarrow> \<not>a_6 = a_1 \<longrightarrow> \<not>a_6 = a_2 \<longrightarrow> \<not>a_6 = a_3 \<longrightarrow> \<not>a_6 = a_4 \<longrightarrow> \<not>a_6 = a_5 \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> t_1 a_8 = (23 :: int) \<longrightarrow> t_1 a_9 = (13 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> -(1 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> (11 :: int) \<longrightarrow> (15 :: int) \<le> i \<longrightarrow> i_1 \<le> (254 :: int) \<longrightarrow> i_1 \<le> (2147483646 :: int) \<longrightarrow> -(2147483600 :: int) \<le> x \<longrightarrow> (48 :: int) \<le> x \<longrightarrow> x \<le> (57 :: int) \<longrightarrow> x \<le> (2147483695 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint8 i_1 \<longrightarrow> is_uint16 i \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> valid_rw t a_6 (1 :: int) \<longrightarrow> is_uint8 ((1 :: int) + i_1) \<longrightarrow> valid_rd t a_8 (1 :: int) \<longrightarrow> valid_rd t a_9 (1 :: int) \<longrightarrow> separated a (1 :: int) a_8 i \<longrightarrow> separated a_1 (1 :: int) a_8 i \<longrightarrow> separated a_2 (1 :: int) a_8 i \<longrightarrow> separated a_3 (1 :: int) a_8 i \<longrightarrow> separated a_4 (1 :: int) a_8 i \<longrightarrow> separated a_5 (1 :: int) a_8 i \<longrightarrow> separated a_6 (1 :: int) a_8 i \<longrightarrow> is_uint8 x \<longrightarrow> valid_rd t a_10 (1 :: int) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_8 i) \<longrightarrow> (\<forall>(i_3 :: int). let x_1 :: int = t_1 (shift a_7 ((2 :: int) + i_3)) in (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> (48 :: int) \<le> x_1 \<and> x_1 \<le> (57 :: int)) \<longrightarrow> (48 :: int) \<le> t_1 (shift a_7 ((2 :: int) + i_2))"
  sorry
end
