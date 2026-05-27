theory fread_Why3_ide_VCfread_call__fread_pre_2_part4_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  shows "let x :: int = t_1 (shift a (9 :: int)) in region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> separated (shift a_2 (0 :: int)) (to_uint32 (i * i_1)) (shift (t_2 (shift a_1 (5 :: int))) (0 :: int)) ((32 :: int) + x)"
  sorry
end
