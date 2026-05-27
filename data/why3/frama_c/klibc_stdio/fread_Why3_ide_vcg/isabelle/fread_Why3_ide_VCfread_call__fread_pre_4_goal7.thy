theory fread_Why3_ide_VCfread_call__fread_pre_4_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "frama_c_klibc_stdio_lib.Axiomatic3_Axiomatic3"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  assumes fact0: "region (base a_1) \<le> (0 :: int)"
  assumes fact1: "region (base a_2) \<le> (0 :: int)"
  assumes fact2: "framed t_2"
  assumes fact3: "linked t"
  shows "p_valid_io_file_pvt t t_2 t_1 a"
  sorry
end
