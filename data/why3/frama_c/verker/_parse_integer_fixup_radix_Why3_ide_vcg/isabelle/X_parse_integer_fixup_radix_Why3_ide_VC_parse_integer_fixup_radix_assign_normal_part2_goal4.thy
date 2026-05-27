theory X_parse_integer_fixup_radix_Why3_ide_VC_parse_integer_fixup_radix_assign_normal_part2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); x :: int = t_2 (shift a (1 :: int)); x_1 :: int = t_3 (shift a (2 :: int)) in t_1 a_1 = (0 :: int) \<longrightarrow> t_2 a_2 = (48 :: int) \<longrightarrow> l_tolower x = (120 :: int) \<longrightarrow> (p_isxdigit x_1 \<longleftrightarrow> \<not>i = (0 :: int)) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint8 i \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> \<not>valid_rd t a_2 (3 :: int)"
  sorry
end
