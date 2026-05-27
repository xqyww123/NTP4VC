theory X__init_stdio_Why3_ide_VC__init_stdio_assign_normal_part3_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_11 :: "addr"
  fixes a_12 :: "addr"
  fixes a_8 :: "addr"
  fixes a_9 :: "addr"
  fixes a_10 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes a_5 :: "addr"
  fixes a :: "addr"
  fixes a_4 :: "addr"
  shows "let x :: int = t_1 (shift a_2 (10 :: int)); x_1 :: int = t_1 (shift a_3 (10 :: int)); x_2 :: int = t_1 (shift a_6 (10 :: int)); x_3 :: int = t_1 (shift a_7 (10 :: int)); x_4 :: int = t_1 (shift a_11 (0 :: int)); x_5 :: int = t_1 (shift a_12 (0 :: int)) in region (base a_8) \<le> (0 :: int) \<longrightarrow> region (base a_9) \<le> (0 :: int) \<longrightarrow> region (base a_10) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> valid_rw t a_8 (3 :: int) \<longrightarrow> valid_rw t a_9 (3 :: int) \<longrightarrow> valid_rw t a_10 (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_sint32 x_5 \<longrightarrow> (Mk_addr (0 :: int) (0 :: int) = a_11 \<longrightarrow> i = (12 :: int)) \<longrightarrow> (Mk_addr (0 :: int) (0 :: int) = a_12 \<longrightarrow> i_1 = (12 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_11 \<longrightarrow> shift a_1 (0 :: int) = a_11) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_12 \<longrightarrow> shift a_5 (0 :: int) = a_12) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_11 \<longrightarrow> x_4 = (0 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_12 \<longrightarrow> x_5 = (1 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_11 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_12 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_4) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_11 \<longrightarrow> x = (1 :: int) \<or> x_1 = (2 :: int)) \<longrightarrow> \<not>(\<not>Mk_addr (0 :: int) (0 :: int) = a_12 \<longrightarrow> x_2 = (1 :: int) \<or> x_3 = (2 :: int))"
  sorry
end
