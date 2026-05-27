theory check_bytes8_Why3_ide_VCcheck_bytes8_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_2 :: int = i_1 + x - x_1; a_3 :: addr = l_check_bytes8 t_1 a_1 i i_1; x_3 :: int = i_1 + x in l_check_bytes8 t_1 a i x_2 = a_3 \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a (shift a_1 i_1) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> (if x_3 = x_1 then Mk_addr (0 :: int) (0 :: int) = a_2 \<and> a_3 = a_2 else \<not>t_1 a = i) \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> t_1 a_4 = i) \<longrightarrow> a_3 = a_2"
  sorry
end
