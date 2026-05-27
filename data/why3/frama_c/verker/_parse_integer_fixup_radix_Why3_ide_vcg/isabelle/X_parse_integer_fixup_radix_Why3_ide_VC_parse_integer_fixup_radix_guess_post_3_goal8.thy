theory X_parse_integer_fixup_radix_Why3_ide_VC_parse_integer_fixup_radix_guess_post_3_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_IntBase_A_IntBase"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_7 :: "addr \<Rightarrow> int"
  fixes t_8 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_12 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  fixes p_2 :: "bool"
  fixes t_9 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes p_1 :: "bool"
  fixes p_3 :: "bool"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes t_10 :: "addr \<Rightarrow> int"
  fixes t_11 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); x :: int = t_5 a_1; x_1 :: int = t_7 a_1; a_3 :: addr = shift a (1 :: int); x_2 :: int = t_8 a_3; x_3 :: int = l_tolower x_2 in t_1 a_1 = (0 :: int) \<longrightarrow> t_8 a_2 = (48 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_8 \<longrightarrow> is_uint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_is_dec t_12 a \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x_2 \<longrightarrow> valid_rd t a_2 (3 :: int) \<longrightarrow> is_sint8 x_3 \<longrightarrow> (if x_3 = (120 :: int) then p = True \<and> p_2 = True \<and> (p_isxdigit (t_9 (shift a (2 :: int))) \<longleftrightarrow> \<not>i = (0 :: int)) \<and> (if i = (0 :: int) then t_3(a_1 := 8 :: int) = t_5 else t_4(a_1 := 16 :: int) = t_5) else p = True \<and> p_2 = True \<and> t_2(a_1 := 8 :: int) = t_5) \<longrightarrow> (if x = (16 :: int) then (p_1 = True \<longleftrightarrow> p = True) \<and> (p_3 = True \<longleftrightarrow> p_2 = True) \<and> t_6 = t_5 \<and> (if t_10 a_2 = (48 :: int) then p_1 = True \<and> p_3 = True \<and> t_11 = t_10 \<and> l_tolower (t_11 a_3) = i_1 else p_1 = True \<and> p_3 = True \<and> t_7 = t_6 \<and> t_12 = t_10) else p = True \<and> p_2 = True \<and> t_7 = t_5) \<longrightarrow> x_1 = (10 :: int)"
  sorry
end
