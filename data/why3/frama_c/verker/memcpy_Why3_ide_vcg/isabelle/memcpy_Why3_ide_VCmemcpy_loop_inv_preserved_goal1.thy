theory memcpy_Why3_ide_VCmemcpy_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_2; x_1 :: int = offset a_1; x_2 :: int = i + x - x_1; a_4 :: addr = shift a_3 (0 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_4 x_2 in \<not>i = (0 :: int) \<longrightarrow> x + offset a_3 = offset a + x_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> addr_le a_3 a \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_2 \<longrightarrow> valid_rw t a_4 x_2 \<longrightarrow> addr_le a (shift a_3 x_2) \<longrightarrow> addr_le a_2 (shift a_1 x_2) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x \<longrightarrow> a_5 (shift a_3 i_1) = a_5 (shift a_1 i_1)) \<longrightarrow> x_1 + to_uint64 (i - (1 :: int)) \<le> i + x"
  sorry
end
