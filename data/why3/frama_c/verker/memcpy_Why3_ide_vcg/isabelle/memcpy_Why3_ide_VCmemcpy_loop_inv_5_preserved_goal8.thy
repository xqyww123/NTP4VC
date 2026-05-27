theory memcpy_Why3_ide_VCmemcpy_loop_inv_5_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal8:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = i_1 + x; x_2 :: int = offset a_2; a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_4 i_1; a_6 :: addr \<Rightarrow> int = a_5(a := a_5 a_2) in \<not>x_1 = x_2 \<longrightarrow> x_2 + offset a_3 = offset a + x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> i + to_uint64 (i_1 + x - (1 :: int) - x_2) < i_1 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> addr_le a_3 a \<longrightarrow> addr_le a (shift a_3 i_1) \<longrightarrow> addr_le a_2 (shift a_1 i_1) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1 \<longrightarrow> valid_rw t a_4 i_1 \<longrightarrow> is_uint64 (i_1 + x - x_2) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x < x_2 \<longrightarrow> a_5 (shift a_3 i_2) = a_5 (shift a_1 i_2)) \<longrightarrow> a_6 (shift a_3 i) = a_6 (shift a_1 i)"
  sorry
end
