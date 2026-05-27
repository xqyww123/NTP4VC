theory X_parse_integer_fixup_radix_Why3_ide_VC_parse_integer_fixup_radix_guess_post_5_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_IntBase_A_IntBase"
begin
theorem goal10:
  fixes a :: "addr"
  fixes t_8 :: "addr \<Rightarrow> int"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_7 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_9 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a (1 :: int); x :: int = t_8 a_3; x_1 :: int = t_6 a_3; x_2 :: int = l_tolower x_1 in t_1 a_1 = (0 :: int) \<longrightarrow> t_5 a_1 = (16 :: int) \<longrightarrow> t_6 a_2 = (48 :: int) \<longrightarrow> t_8 a_2 = (48 :: int) \<longrightarrow> l_tolower x = (120 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_6 \<longrightarrow> is_uint8 i \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x \<longrightarrow> valid_rd t a_2 (3 :: int) \<longrightarrow> is_sint8 x_2 \<longrightarrow> (if x_2 = (120 :: int) then (p_isxdigit (t_7 (shift a (2 :: int))) \<longleftrightarrow> \<not>i = (0 :: int)) \<and> (if i = (0 :: int) then t_3(a_1 := 8 :: int) = t_5 else t_4(a_1 := 16 :: int) = t_5) else t_2(a_1 := 8 :: int) = t_5) \<longrightarrow> \<not>(p_is_oct t_9 a \<or> p_is_dec t_9 a)"
  sorry
end
