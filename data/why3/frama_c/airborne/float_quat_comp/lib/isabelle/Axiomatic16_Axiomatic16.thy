theory Axiomatic16_Axiomatic16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "S9_RealVect3_s_S9_RealVect3_s" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat"
begin
definition l_scalar_product :: "s9_realvect3_s \<Rightarrow> s9_realvect3_s \<Rightarrow> real"
  where "l_scalar_product v1_0 v2_0 = f9_realvect3_s_x v1_0 * f9_realvect3_s_x v2_0 + f9_realvect3_s_y v1_0 * f9_realvect3_s_y v2_0 + f9_realvect3_s_z v1_0 * f9_realvect3_s_z v2_0" for v1_0 v2_0
definition l_mult_scalar_1' :: "real \<Rightarrow> s9_realvect3_s \<Rightarrow> s9_realvect3_s"
  where "l_mult_scalar_1' scal_0 v = s9_realvect3_s'mk (scal_0 * f9_realvect3_s_x v) (scal_0 * f9_realvect3_s_y v) (scal_0 * f9_realvect3_s_z v)" for scal_0 v
definition l_add_realvect3 :: "s9_realvect3_s \<Rightarrow> s9_realvect3_s \<Rightarrow> s9_realvect3_s"
  where "l_add_realvect3 v1_0 v2_0 = s9_realvect3_s'mk (f9_realvect3_s_x v1_0 + f9_realvect3_s_x v2_0) (f9_realvect3_s_y v1_0 + f9_realvect3_s_y v2_0) (f9_realvect3_s_z v1_0 + f9_realvect3_s_z v2_0)" for v1_0 v2_0
definition l_cross_product :: "s9_realvect3_s \<Rightarrow> s9_realvect3_s \<Rightarrow> s9_realvect3_s"
  where "l_cross_product v1_0 v2_0 = (let r :: real = f9_realvect3_s_z v1_0; r_1 :: real = f9_realvect3_s_y v2_0; r_2 :: real = f9_realvect3_s_y v1_0; r_3 :: real = f9_realvect3_s_z v2_0; r_4 :: real = f9_realvect3_s_x v1_0; r_5 :: real = f9_realvect3_s_x v2_0 in s9_realvect3_s'mk (-(r * r_1) + r_2 * r_3) (-(r_4 * r_3) + r * r_5) (-(r_2 * r_5) + r_4 * r_1))" for v1_0 v2_0
end
