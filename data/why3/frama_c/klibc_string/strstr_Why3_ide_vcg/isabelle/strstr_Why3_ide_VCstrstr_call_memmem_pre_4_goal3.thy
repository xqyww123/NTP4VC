theory strstr_Why3_ide_VCstrstr_call_memmem_pre_4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = l_length t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 (l_length t_1 a_1) \<longrightarrow> p_length_of_str_is t t_1 a i \<longrightarrow> p_length_of_str_is t t_1 a_1 i_1 \<longrightarrow> valid_rw t (shift a (0 :: int)) (to_uint32 x)"
  sorry
end
