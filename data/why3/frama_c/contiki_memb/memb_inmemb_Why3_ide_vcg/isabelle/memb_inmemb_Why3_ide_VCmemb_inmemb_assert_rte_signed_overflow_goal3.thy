theory memb_inmemb_Why3_ide_VCmemb_inmemb_assert_rte_signed_overflow_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_contiki_memb_lib.Axiomatic13_Axiomatic13" "Why3STD.Memory_Memory" "frama_c_contiki_memb_lib.Compound_Compound" "frama_c_contiki_memb_lib.A_OccArray_A_OccArray" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a_1 (1 :: int)); x_1 :: int = t_1 (shift a_1 (0 :: int)); a_2 :: addr = shift a_1 (3 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 x \<longrightarrow> is_uint16 x_1 \<longrightarrow> p_valid_memb t t_2 t_1 a_1 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> addr_le (t_2 a_2) a \<longrightarrow> -(2147483648 :: int) \<le> x * x_1"
  sorry
end
