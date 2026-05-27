theory partial_sum_Why3_ide_VCpartial_sum_loop_assign_part3_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sum_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sum_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic_Axiomatic"
begin
theorem goal16:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); x :: int = t_2 a_3; a_4 :: addr = shift a (1 :: int); x_1 :: int = i - (1 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_2 := x)) a_4 x_1; x_2 :: int = i_1 - (1 :: int); a_6 :: int = a_5 (shift a x_2); a_7 :: addr = shift a_1 i_1; a_8 :: int = a_5 a_7; a_9 :: addr = shift a (to_uint32 x_2); a_10 :: int = a_5 a_9; a_11 :: int = a_8 + a_10; a_12 :: addr = shift a i_1 in a_6 = l_accumulate_1' a_5 a_1 i_1 (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> -(2147483648 :: int) \<le> a_11 \<longrightarrow> a_11 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_12 (1 :: int) \<longrightarrow> \<not>invalid t a_12 (1 :: int) \<longrightarrow> p_accumulatebounds_1' t_2 a_1 ((1 :: int) + i) (0 :: int) \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> valid_rd t a_9 (1 :: int) \<longrightarrow> is_sint32 a_8 \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_10 \<longrightarrow> p_unchanged_1' a_5 t_2 a_1 (0 :: int) i \<longrightarrow> p_partialsum a_5 a_1 i_1 a \<longrightarrow> included a_12 (1 :: int) a_4 x_1"
  sorry
end
