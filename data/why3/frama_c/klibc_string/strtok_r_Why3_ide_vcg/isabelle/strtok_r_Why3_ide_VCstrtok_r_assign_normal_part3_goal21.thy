theory strtok_r_Why3_ide_VCstrtok_r_assign_normal_part3_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_string_lib.Axiomatic_Axiomatic" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.A_Length_A_Length"
begin
theorem goal21:
  shows "let a :: addr = shift (Mk_addr (0 :: int) (0 :: int)) (0 :: int) in \<forall>(i_1 :: int) (i :: int) (t :: int \<Rightarrow> int) (t_1 :: addr \<Rightarrow> int) (t_2 :: addr \<Rightarrow> addr) (a_2 :: addr) (a_1 :: addr). let a_3 :: addr = shift a_2 (0 :: int); x :: int = (1 :: int) + l_length t_1 a_2; x_1 :: int = (1 :: int) + l_length t_1 (Mk_addr (0 :: int) (0 :: int)) in region (0 :: int) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t (t_2 a_1) (1 :: int) \<longrightarrow> p_length_of_str_is t t_1 a_2 i \<longrightarrow> p_length_of_str_is t t_1 a_2 i_1 \<longrightarrow> separated a_1 (1 :: int) a_3 x \<longrightarrow> separated a_1 (1 :: int) a x_1 \<longrightarrow> \<not>separated a x_1 a_3 x"
  sorry
end
