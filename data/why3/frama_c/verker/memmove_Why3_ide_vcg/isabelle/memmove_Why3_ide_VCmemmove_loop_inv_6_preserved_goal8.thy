theory memmove_Why3_ide_VCmemmove_loop_inv_6_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_3 :: addr = shift a_2 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i_1; a_5 :: addr \<Rightarrow> int = a_4(a_2 := a_4 a_1); x :: int = to_uint64 (i_1 - (1 :: int)); x_1 :: int = i_1 - (1 :: int) - x; a_6 :: int = a_5 (shift a_2 x_1); a_7 :: int = a_5 (shift a x_1) in \<not>i_1 = (0 :: int) \<longrightarrow> offset a_1 = offset a \<longrightarrow> a_6 = a_7 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> i + x < i_1 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> addr_le a_1 (shift a i_1) \<longrightarrow> addr_le a_2 (shift a_2 i_1) \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> is_sint8 a_7 \<longrightarrow> is_sint8 a_6 \<longrightarrow> (\<forall>(i_2 :: int). let a_8 :: addr = shift a i_2 in (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> a_4 a_8 = t_2 a_8) \<longrightarrow> a_5 (shift a_2 i) = t_2 (shift a i)"
  sorry
end
