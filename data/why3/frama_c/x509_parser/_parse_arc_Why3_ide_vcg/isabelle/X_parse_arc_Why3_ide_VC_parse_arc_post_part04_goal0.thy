theory X_parse_arc_Why3_ide_VC_parse_arc_post_part04_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_x509_parser_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = base a_2; a_3 :: addr = shift a_1 i; x_3 :: int = t_1 a_3; x_4 :: int = land (127 :: int) x_3; x_5 :: int = lsl i_2 (7 :: int); x_6 :: int = x_5 + x_4 in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>a_2 = a \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_1 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> i_2 < lsl (1 :: int) (to_uint32 ((7 :: int) * i)) \<longrightarrow> (0 :: int) \<le> x_6 \<longrightarrow> -(1 :: int) \<le> i \<longrightarrow> i \<le> (3 :: int) \<longrightarrow> i \<le> (4 :: int) \<longrightarrow> (5 :: int) \<le> i_1 \<longrightarrow> i \<le> (65534 :: int) \<longrightarrow> i \<le> (2147483646 :: int) \<longrightarrow> x_5 \<le> (4294967295 :: int) \<longrightarrow> x_6 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> is_uint16 ((1 :: int) + i) \<longrightarrow> is_uint32 x_5 \<longrightarrow> is_uint8 x_3 \<longrightarrow> \<not>bit_test x_3 (7 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> is_uint32 x_4 \<longrightarrow> ((0 :: int) < i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> bit_test (t_1 (shift a_1 i_3)) (7 :: int)) \<longrightarrow> i < i_1"
  sorry
end
