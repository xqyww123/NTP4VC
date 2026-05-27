theory fopen_Why3_ide_VCfopen_post_part3_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Globals_Globals" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes a_4 :: "addr"
  shows "let a_7 :: addr = shift a_1 (0 :: int); x :: int = t_1 (shift a_7 (0 :: int)); x_1 :: int = t_1 (shift a_2 (10 :: int)); x_2 :: int = t_1 (shift a_3 (10 :: int)); m :: int \<Rightarrow> int = t(38235 :: int := 1 :: int) in \<not>a_7 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 (Mk_addr (38235 :: int) (0 :: int)) = (438 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> p_length_of_str_is t t_2 a_5 i \<longrightarrow> p_length_of_str_is t t_2 a_5 i_3 \<longrightarrow> p_length_of_str_is t t_2 a_5 i_4 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_1 \<longrightarrow> p_length_of_str_is t t_2 a_6 i_2 \<longrightarrow> p_valid_io_file_pvt m t_3 t_1 a \<longrightarrow> is_sint32 x \<longrightarrow> x_1 = (1 :: int) \<or> x_2 = (2 :: int) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a_5 \<or> (\<exists>(i_5 :: int). p_length_of_str_is m t_2 a_5 i_5) \<longrightarrow> p_valid_file m t_1 a_7 \<and> p_valid_io_file_pvt m t_3 t_1 a_4"
  sorry
end
