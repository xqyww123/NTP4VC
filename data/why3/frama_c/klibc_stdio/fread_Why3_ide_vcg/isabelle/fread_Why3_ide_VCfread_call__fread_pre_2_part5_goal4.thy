theory fread_Why3_ide_VCfread_call__fread_pre_2_part5_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_klibc_stdio_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  shows "let x :: int = t_1 (shift a (9 :: int)) in region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 x \<longrightarrow> separated (t_2 (shift a_2 (4 :: int))) (11 :: int) (shift (t_2 (shift a_1 (5 :: int))) (0 :: int)) ((32 :: int) + x)"
  sorry
end
