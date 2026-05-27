theory fdopen_Why3_ide_VCfdopen_assign_normal_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_stdio_lib.Axiomatic_Axiomatic" "frama_c_klibc_stdio_lib.Compound_Compound"
begin
theorem goal1:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "is_sint32 i"
  shows "\<not>(Mk_addr (0 :: int) (0 :: int) = a \<or> (\<exists>(i_1 :: int). p_length_of_str_is t t_1 a i_1))"
  sorry
end
