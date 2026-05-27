theory X__init_stdio_Why3_ide_VC__init_stdio_assign_normal_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_7 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let x :: int = t_1 (shift a_2 (10 :: int)); x_1 :: int = t_1 (shift a_3 (10 :: int)); x_2 :: int = t_1 (shift a_7 (0 :: int)) in region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> region (base a_6) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rw t a_4 (3 :: int) \<longrightarrow> valid_rw t a_5 (3 :: int) \<longrightarrow> valid_rw t a_6 (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_sint32 x_2 \<longrightarrow> (Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> i = (12 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> shift a_1 (0 :: int) = a_7) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> (\<not>Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a) \<longrightarrow> \<not>(\<not>Mk_addr (0 :: int) (0 :: int) = a_7 \<longrightarrow> x = (1 :: int) \<or> x_1 = (2 :: int))"
  sorry
end
