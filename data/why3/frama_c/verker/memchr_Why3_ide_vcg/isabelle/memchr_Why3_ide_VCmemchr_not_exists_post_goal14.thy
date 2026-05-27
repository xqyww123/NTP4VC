theory memchr_Why3_ide_VCmemchr_not_exists_post_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal14:
  fixes a_5 :: "addr"
  fixes a_9 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_8 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_10 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  shows "let x :: int = offset a_5; x_1 :: int = offset a_9; x_2 :: int = i + x; x_3 :: int = to_uint8 i_1 in x \<le> x_1 \<longrightarrow> region (base a_8) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_6 a_9 \<longrightarrow> addr_le a_9 (shift a_7 i) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> is_uint64 (i + x - x_1) \<longrightarrow> (if x_2 = x_1 then Mk_addr (0 :: int) (0 :: int) = a_10 else t_1 a_9 = x_3) \<longrightarrow> (\<forall>(a_11 :: addr). addr_lt a_11 a_9 \<longrightarrow> addr_le a_4 a_11 \<longrightarrow> \<not>t_1 a_11 = x_3) \<longrightarrow> (\<forall>(a_11 :: addr). addr_le a_2 a_11 \<longrightarrow> addr_lt a_11 (shift a_3 i) \<longrightarrow> \<not>t_1 a_11 = x_3) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a_10"
  sorry
end
