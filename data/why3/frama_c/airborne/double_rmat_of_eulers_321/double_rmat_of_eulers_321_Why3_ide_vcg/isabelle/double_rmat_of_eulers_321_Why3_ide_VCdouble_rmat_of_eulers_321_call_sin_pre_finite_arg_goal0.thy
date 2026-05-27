theory double_rmat_of_eulers_321_Why3_ide_VCdouble_rmat_of_eulers_321_call_sin_pre_finite_arg_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_double_rmat_of_eulers_321_lib.Axiomatic19_Axiomatic19" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_double_rmat_of_eulers_321_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let r :: real = t_1 (shift a (0 :: int)) in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> p_rvalid_doubleeulers t t_1 a \<longrightarrow> is_float64 r \<longrightarrow> is_float64 (t_1 (shift a (2 :: int))) \<longrightarrow> is_float64 (t_1 (shift a (1 :: int))) \<longrightarrow> is_finite64 r"
  sorry
end
