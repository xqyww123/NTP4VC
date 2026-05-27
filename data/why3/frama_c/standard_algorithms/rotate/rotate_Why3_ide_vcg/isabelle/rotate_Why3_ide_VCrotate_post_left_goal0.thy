theory rotate_Why3_ide_VCrotate_post_left_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_rotate_lib.Compound_Compound" "frama_c_standard_algorithms_rotate_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes t_7 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = i_1 - i; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a x in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> (if i < i_1 then if (0 :: int) < i then havoc t_3 t_5 a_1 i_1 = t_7 \<and> havoc t_1 t_6 a_1 x = t_4 \<and> havoc t_2 t_4 a_2 i = t_5 \<and> valid_rw t a_1 x \<and> p_reverse_5' t_4 t_6 a (0 :: int) x \<and> valid_rw t a_2 i \<and> p_reverse_4' t_5 t_6 a (0 :: int) x (0 :: int) \<and> p_reverse_4' t_5 t_6 a x i_1 x \<and> p_reverse_4' t_7 t_5 a (0 :: int) x i \<and> p_reverse_4' t_7 t_5 a x i_1 (0 :: int) \<and> p_reverse_5' t_5 t_4 a_2 (0 :: int) i else t_7 = t_6 else t_7 = t_6) \<longrightarrow> p_equalranges_4' t_7 t_6 a (0 :: int) x i"
  sorry
end
