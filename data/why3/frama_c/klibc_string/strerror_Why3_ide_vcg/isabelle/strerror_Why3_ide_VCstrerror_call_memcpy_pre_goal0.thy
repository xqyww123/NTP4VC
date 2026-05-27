theory strerror_Why3_ide_VCstrerror_call_memcpy_pre_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound" "frama_c_klibc_string_lib.Globals_Globals"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  shows "let x :: int = to_uint32 i in to_uint32 (i_1 cdiv (10 :: int)) = (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i_1 \<longrightarrow> separated (shift a (-(1 :: int))) x (shift (Mk_addr (16590 :: int) (0 :: int)) (6 :: int)) x"
  sorry
end
