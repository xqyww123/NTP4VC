theory X_parse_integer_Why3_ide_VC_parse_integer_call_div_u64_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "Why3STD.Cbits_Cbits" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes p_2 :: "bool"
  fixes p_1 :: "bool"
  fixes p :: "bool"
  shows "let x :: int = t_2 a_1; x_1 :: int = t_3 a_1; x_2 :: int = t_4 a_1; x_3 :: int = to_uint32 (i_6 - (87 :: int)) in \<not>x = (0 :: int) \<longrightarrow> i_2 cmod (2 :: int) = (0 :: int) \<longrightarrow> \<not>land (17293822569102704640 :: int) i_1 = (0 :: int) \<longrightarrow> i < (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (16 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 i_3 \<longrightarrow> is_sint8 i_4 \<longrightarrow> is_sint8 i_5 \<longrightarrow> is_sint8 i_6 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint64 i_1 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> \<not>(if (48 :: int) \<le> x then (p_2 = True \<longleftrightarrow> p_1 = True) \<and> t_3 = t_2 \<and> (if x_1 \<le> (57 :: int) then t_4 = t_3 \<and> to_uint32 (x_2 - (48 :: int)) = i else p = False \<and> p_2 = True \<and> x_3 = i \<and> (97 :: int) \<le> i_4 \<and> i_5 \<le> (102 :: int)) else p = False \<and> p_1 = False \<and> x_3 = i \<and> (97 :: int) \<le> i_3 \<and> i_5 \<le> (102 :: int))"
  sorry
end
