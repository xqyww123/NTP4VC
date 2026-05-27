theory memmove_Why3_ide_VCmemmove_loop_assign_part7_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal21:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_2 :: int = i + x_1; a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i; a_5 :: addr \<Rightarrow> int = a_4(a_2 := a_4 a_1); x_4 :: int = i - (1 :: int) - to_uint64 (i + x_1 - (1 :: int) - x); a_6 :: int = a_5 (shift a_2 x_4); a_7 :: int = a_5 (shift a x_4) in x = x_1 \<longrightarrow> \<not>x_2 = x \<longrightarrow> a_6 = a_7 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x \<le> x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> \<not>invalid t a_2 (1 :: int) \<longrightarrow> addr_le a_1 (shift a i) \<longrightarrow> addr_le a_2 (shift a_2 i) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> is_uint64 (i + x_1 - x) \<longrightarrow> is_sint8 a_7 \<longrightarrow> is_sint8 a_6 \<longrightarrow> (\<forall>(i_1 :: int). let a_8 :: addr = shift a i_1 in i_1 < i \<longrightarrow> x \<le> i_1 + x_1 \<longrightarrow> a_4 a_8 = t_2 a_8) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x \<longrightarrow> a_4 (shift a_2 i_1) = t_2 (shift a i_1)) \<longrightarrow> (0 :: int) < i"
  sorry
end
