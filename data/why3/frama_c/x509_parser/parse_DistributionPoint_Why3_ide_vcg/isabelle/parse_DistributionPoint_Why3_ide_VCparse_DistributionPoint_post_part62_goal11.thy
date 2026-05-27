theory parse_DistributionPoint_Why3_ide_VCparse_DistributionPoint_post_part62_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits"
begin
theorem goal11:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_2; x_1 :: int = base a; x_2 :: int = base a_1; a_3 :: addr = shift a_2 i_4; x_3 :: int = i + i_4; a_4 :: addr = shift a_1 (12 :: int); m :: addr \<Rightarrow> int = t_1(a := x_3); x_4 :: int = m a_4; x_5 :: int = (m(a_4 := lor (1 :: int) x_4)) a in \<not>i = (0 :: int) \<longrightarrow> \<not>i_3 = (0 :: int) \<longrightarrow> \<not>Mk_addr (0 :: int) (0 :: int) = a_2 \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x = x_2 \<longrightarrow> \<not>a_3 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 < (0 :: int) \<longrightarrow> i_2 < (0 :: int) \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i \<le> i_3 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> x_3 \<le> i_3 \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) \<le> i_4 \<longrightarrow> -(2147483648 :: int) \<le> x_3 \<longrightarrow> x_3 \<le> (65535 :: int) \<longrightarrow> x_3 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> is_uint16 i_3 \<longrightarrow> is_uint16 i_4 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> valid_rw t a_1 (15 :: int) \<longrightarrow> separated a (1 :: int) a_1 (15 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_uint16 x_5 \<longrightarrow> ((0 :: int) < i_3 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_3) \<longrightarrow> ((0 :: int) < i \<longrightarrow> valid_rd t a_3 i) \<longrightarrow> x_5 \<le> i_3"
  sorry
end
