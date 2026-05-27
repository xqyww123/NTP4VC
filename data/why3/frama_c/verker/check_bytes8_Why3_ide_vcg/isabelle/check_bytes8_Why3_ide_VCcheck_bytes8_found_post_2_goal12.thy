theory check_bytes8_Why3_ide_VCcheck_bytes8_found_post_2_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal12:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = offset a_2; x_2 :: int = offset a_1; x_3 :: int = i + x_1 - x_2; a_4 :: addr = l_check_bytes8 t_1 a_2 x i; x_4 :: int = i + x_1; x_5 :: int = t_1 a_1; a_5 :: addr = shift a_2 i in \<not>t_1 a_3 = x \<longrightarrow> l_check_bytes8 t_1 a_1 x x_3 = a_4 \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_4 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_uint8 x \<longrightarrow> is_uint8 x_5 \<longrightarrow> addr_lt a_3 a_5 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i \<longrightarrow> is_uint32 x_3 \<longrightarrow> (if x_4 = x_2 then a_4 = Mk_addr (0 :: int) (0 :: int) else \<not>x_5 = x) \<longrightarrow> \<not>(\<forall>(a_6 :: addr). addr_lt a_6 a_1 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> x = t_1 a_6)"
  sorry
end
