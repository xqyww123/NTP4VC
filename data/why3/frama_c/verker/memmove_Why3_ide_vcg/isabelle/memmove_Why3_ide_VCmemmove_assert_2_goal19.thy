theory memmove_Why3_ide_VCmemmove_assert_2_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal19:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_3 :: int = x - x_1; a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr = shift a_2 x_3; a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 x_3; x_4 :: int = x - (1 :: int) - x_1; a_6 :: addr \<Rightarrow> int = a_5(shift a_2 x_4 := a_5 (shift a_1 (-(1 :: int)))); x_5 :: int = to_uint64 x_4; a_7 :: int = a_6 (shift a x_5); a_8 :: int = a_6 (shift a_2 x_5) in \<not>x = x_1 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a a_1 \<longrightarrow> \<not>addr_le a_2 a \<longrightarrow> is_uint64 x_3 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_3 \<longrightarrow> valid_rw t a_3 x_3 \<longrightarrow> addr_le a_1 (shift a x_3) \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> addr_le a_4 a_4 \<longrightarrow> is_sint8 a_7 \<longrightarrow> is_sint8 a_8 \<longrightarrow> (\<forall>(i :: int). let a_9 :: addr = shift a i in (0 :: int) \<le> i \<longrightarrow> i + x_1 < x \<longrightarrow> a_5 a_9 = t_2 a_9) \<longrightarrow> a_8 = a_7"
  sorry
end
