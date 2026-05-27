theory X_parse_integer_fixup_radix_Why3_ide_VC_parse_integer_fixup_radix_assign_exit_part7_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal2:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_9 :: "addr \<Rightarrow> int"
  fixes t_10 :: "addr \<Rightarrow> int"
  fixes t_11 :: "addr \<Rightarrow> int"
  fixes t_7 :: "addr \<Rightarrow> int"
  fixes t_12 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_8 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); x :: int = t_1 a_1; x_1 :: int = t_9 a_2; x_2 :: int = t_10 (shift a (1 :: int)); x_3 :: int = t_11 (shift a (2 :: int)) in t_7 a_1 = (16 :: int) \<longrightarrow> t_12 a_2 = (48 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_8 \<longrightarrow> is_uint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> valid_rd t a_2 (3 :: int) \<longrightarrow> \<not>(if x = (0 :: int) then t_2 = t_1 \<and> t_9 = t_8 \<and> (if x_1 = (48 :: int) then t_10 = t_9 \<and> l_tolower x_2 = i_1 \<and> (if i_1 = (120 :: int) then (p_isxdigit x_3 \<longleftrightarrow> \<not>i = (0 :: int)) \<and> (if i = (0 :: int) then t_5(a_1 := 8 :: int) = t_7 else t_6(a_1 := 16 :: int) = t_7) else t_4(a_1 := 8 :: int) = t_7) else t_3 = t_2 \<and> t_12 = t_9 \<and> t_3(a_1 := 10 :: int) = t_7) else t_7 = t_1 \<and> t_12 = t_8)"
  sorry
end
