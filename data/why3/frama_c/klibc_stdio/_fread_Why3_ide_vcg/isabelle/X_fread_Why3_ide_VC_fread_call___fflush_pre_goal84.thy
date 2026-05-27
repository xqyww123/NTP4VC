theory X_fread_Why3_ide_VC_fread_call___fflush_pre_goal84
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal84:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_12 :: "addr"
  fixes a :: "addr"
  fixes a_6 :: "addr"
  fixes a_13 :: "addr"
  fixes t_3 :: "addr \<Rightarrow> addr"
  fixes a_3 :: "addr"
  fixes a_9 :: "addr"
  fixes a_2 :: "addr"
  fixes a_8 :: "addr"
  fixes a_1 :: "addr"
  fixes a_7 :: "addr"
  fixes i :: "int"
  fixes a_10 :: "addr"
  fixes a_4 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes a_11 :: "addr"
  shows "let x :: int = t_1 (shift a_12 (8 :: int)); x_1 :: int = t_1 (shift a (9 :: int)); x_2 :: int = t_1 (shift a_6 (9 :: int)); a_14 :: addr = shift a_13 (0 :: int); a_15 :: addr = t_3 (shift a_3 (4 :: int)); a_16 :: addr = t_3 (shift a_9 (4 :: int)); a_17 :: addr = t_3 (shift a_2 (3 :: int)); a_18 :: addr = t_3 (shift a_8 (3 :: int)); a_19 :: addr = shift (t_3 (shift a_1 (5 :: int))) (0 :: int); x_3 :: int = (32 :: int) + x_1; a_20 :: addr = shift (t_3 (shift a_7 (5 :: int))) (0 :: int); x_4 :: int = (32 :: int) + x_2 in \<not>i = (0 :: int) \<longrightarrow> shift a_10 (0 :: int) = shift a_4 (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a_10) \<le> (0 :: int) \<longrightarrow> region (base a_13) \<le> (0 :: int) \<longrightarrow> framed t_3 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_uint32 x \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_5 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_11 \<longrightarrow> valid_rw t a_14 i \<longrightarrow> separated a_14 i a_15 (11 :: int) \<longrightarrow> separated a_14 i a_16 (11 :: int) \<longrightarrow> separated a_14 i a_17 (11 :: int) \<longrightarrow> separated a_14 i a_18 (11 :: int) \<longrightarrow> separated a_15 (11 :: int) a_17 (11 :: int) \<longrightarrow> separated a_16 (11 :: int) a_18 (11 :: int) \<longrightarrow> separated a_14 i a_19 x_3 \<longrightarrow> separated a_14 i a_20 x_4 \<longrightarrow> separated a_15 (11 :: int) a_19 x_3 \<longrightarrow> separated a_16 (11 :: int) a_20 x_4 \<longrightarrow> separated a_17 (11 :: int) a_19 x_3 \<longrightarrow> separated a_18 (11 :: int) a_20 x_4 \<longrightarrow> p_valid_io_file_pvt t t_3 t_1 a_12"
  sorry
end
