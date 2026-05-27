theory fread_Why3_ide_VCfread_call__fread_pre_5_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "framed t_1"
  assumes fact3: "linked t"
  assumes fact4: "is_uint32 i"
  assumes fact5: "is_uint32 i_1"
  shows "valid_rw t (shift a (0 :: int)) (to_uint32 (i * i_1))"
  sorry
end
