theory memccpy_Why3_ide_VCmemccpy_exists_c_assign_part05_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.A_PosOfChar_A_PosOfChar" "frama_c_klibc_string_lib.Axiomatic1_Axiomatic1" "frama_c_klibc_string_lib.A_Length_A_Length" "frama_c_klibc_string_lib.Axiomatic_Axiomatic"
begin
theorem goal18:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int) in t_1 (shift a i_2) = to_sint8 i_3 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i < i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> -(128 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> (127 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_3 i_1 \<longrightarrow> \<not>invalid t a_3 (i_1 - i) \<longrightarrow> separated a_2 i_1 a_3 i_1 \<longrightarrow> i_1 \<le> (1 :: int) + i + l_posofchar t_1 a i_3"
  sorry
end
