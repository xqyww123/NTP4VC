theory double_rmat_of_eulers_321_Why3_ide_VCdouble_rmat_of_eulers_321_call_sin_pre_finite_arg_3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_airborne_double_rmat_of_eulers_321_lib.Axiomatic19_Axiomatic19" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "frama_c_airborne_double_rmat_of_eulers_321_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> real"
  fixes a :: "addr"
  fixes r :: "real"
  fixes r_1 :: "real"
  fixes r_2 :: "real"
  fixes r_3 :: "real"
  fixes t :: "int \<Rightarrow> int"
  shows "let r_4 :: real = t_1 (shift a (0 :: int)); r_5 :: real = t_1 (shift a (1 :: int)); r_6 :: real = t_1 (shift a (2 :: int)) in r \<le> (1 :: Real.real) \<longrightarrow> r_1 \<le> (1 :: Real.real) \<longrightarrow> r_2 \<le> (1 :: Real.real) \<longrightarrow> r_3 \<le> (1 :: Real.real) \<longrightarrow> -(1 :: Real.real) \<le> r \<longrightarrow> -(1 :: Real.real) \<le> r_1 \<longrightarrow> -(1 :: Real.real) \<le> r_2 \<longrightarrow> -(1 :: Real.real) \<le> r_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_finite64 r \<longrightarrow> is_finite64 r_1 \<longrightarrow> is_finite64 r_2 \<longrightarrow> is_finite64 r_3 \<longrightarrow> is_float64 r \<longrightarrow> is_float64 r_1 \<longrightarrow> is_float64 r_2 \<longrightarrow> is_float64 r_3 \<longrightarrow> p_rvalid_doubleeulers t t_1 a \<longrightarrow> is_finite64 r_4 \<longrightarrow> is_finite64 r_5 \<longrightarrow> is_float64 r_4 \<longrightarrow> is_float64 r_6 \<longrightarrow> is_float64 r_5 \<longrightarrow> is_finite64 r_6"
  sorry
end
