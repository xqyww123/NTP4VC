theory X__init_stdio_Why3_ide_VC__init_stdio_assign_exit_part3_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_9 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_8 :: "addr"
  fixes t_4 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_10 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let x :: int = t_1 (shift a_2 (10 :: int)); x_1 :: int = t_1 (shift a_3 (10 :: int)); x_2 :: int = t_1 (shift a_9 (0 :: int)) in region (base a_6) \<le> (0 :: int) \<longrightarrow> region (base a_7) \<le> (0 :: int) \<longrightarrow> region (base a_8) \<le> (0 :: int) \<longrightarrow> framed t_4 \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> valid_rw t a_6 (3 :: int) \<longrightarrow> valid_rw t a_7 (3 :: int) \<longrightarrow> valid_rw t a_8 (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 (t_2 (shift a_4 (10 :: int))) \<longrightarrow> is_uint32 (t_2 (shift a_5 (10 :: int))) \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 (t_2 (shift a_10 (0 :: int))) \<longrightarrow> (Mk_addr (0 :: int) (0 :: int) = a_9 \<longrightarrow> i_1 = (12 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_9 \<longrightarrow> shift a_1 (0 :: int) = a_9) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_9 \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_9 \<longrightarrow> p_valid_io_file_pvt t t_4 t_1 a) \<longrightarrow> \<not>(\<not>Mk_addr (0 :: int) (0 :: int) = a_9 \<longrightarrow> x = (1 :: int) \<or> x_1 = (2 :: int))"
  sorry
end
