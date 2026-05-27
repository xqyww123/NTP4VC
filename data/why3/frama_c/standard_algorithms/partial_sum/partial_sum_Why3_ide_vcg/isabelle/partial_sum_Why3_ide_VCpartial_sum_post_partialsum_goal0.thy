theory partial_sum_Why3_ide_VCpartial_sum_post_partialsum_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sum_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sum_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> p_accumulatebounds_1' t_3 a_1 ((1 :: int) + i_1) (0 :: int) \<longrightarrow> separated a_2 i_1 a_3 i_1 \<longrightarrow> (if (0 :: int) < i_1 then p = False \<and> i_1 = i \<and> i_2 = i \<and> i_2 = i_1 \<and> t_2 (shift a (i_3 - (1 :: int))) = l_accumulate_1' t_2 a_1 i_3 (0 :: int) \<and> havoc t_1 (t_3(a_3 := t_3 a_2)) (shift a (1 :: int)) (i_1 - (1 :: int)) = t_2 \<and> (0 :: int) < i_3 \<and> i_3 \<le> i_1 \<and> i_1 \<le> i_3 \<and> p_unchanged_1' t_2 t_3 a_1 (0 :: int) i_1 \<and> p_partialsum t_2 a_1 i_3 a \<and> valid_rd t a_2 (1 :: int) \<and> valid_rw t a_3 (1 :: int) else t_3 = t_2) \<longrightarrow> p_partialsum t_2 a_1 i_1 a"
  sorry
end
