theory check_bytes8_Why3_ide_VCcheck_bytes8_found_post_3_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal13:
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  shows "let x :: int = offset a_2; x_1 :: int = offset a_1; x_2 :: int = i_1 + x - x_1; a_5 :: addr = l_check_bytes8 t_1 a_2 i i_1; x_3 :: int = i_1 + x; x_4 :: int = t_1 a_1; a_6 :: addr = shift a_2 i_1 in \<not>t_1 a_3 = i \<longrightarrow> l_check_bytes8 t_1 a_1 i x_2 = a_5 \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> addr_lt a_4 a \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> is_uint8 x_4 \<longrightarrow> addr_lt a_3 a_6 \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> valid_rd t (shift a_2 (0 :: int)) i_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> (if x_3 = x_1 then a_5 = Mk_addr (0 :: int) (0 :: int) else \<not>x_4 = i) \<longrightarrow> (\<forall>(a_7 :: addr). addr_lt a_7 a_1 \<longrightarrow> addr_le a_2 a_7 \<longrightarrow> t_1 a_7 = i) \<longrightarrow> t_1 a_4 = i"
  sorry
end
