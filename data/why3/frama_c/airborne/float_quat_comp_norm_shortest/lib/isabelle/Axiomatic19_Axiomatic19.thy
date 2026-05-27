theory Axiomatic19_Axiomatic19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S12_RealQuatVect_s_S12_RealQuatVect_s" "S9_RealVect3_s_S9_RealVect3_s" "Compound_Compound" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat" "Axiomatic16_Axiomatic16"
begin
definition l_l_quatvect_of_floatquat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s12_realquatvect_s"
  where "l_l_quatvect_of_floatquat mflt_0 q = s12_realquatvect_s'mk (mflt_0 (shift q (0 :: int))) (s9_realvect3_s'mk (mflt_0 (shift q (1 :: int))) (mflt_0 (shift q (2 :: int))) (mflt_0 (shift q (3 :: int))))" for mflt_0 q
definition l_mult_realquatvect :: "s12_realquatvect_s \<Rightarrow> s12_realquatvect_s \<Rightarrow> s12_realquatvect_s"
  where "l_mult_realquatvect q1_0 q2_0 = (let a :: s9_realvect3_s = f12_realquatvect_s_vect q1_0; a_1 :: s9_realvect3_s = f12_realquatvect_s_vect q2_0; r :: real = f12_realquatvect_s_scalar q1_0; r_1 :: real = f12_realquatvect_s_scalar q2_0 in s12_realquatvect_s'mk (-l_scalar_product a a_1 + r * r_1) (l_add_realvect3 (l_add_realvect3 (l_mult_scalar_1' r a_1) (l_mult_scalar_1' r_1 a)) (l_cross_product a a_1)))" for q1_0 q2_0
end
