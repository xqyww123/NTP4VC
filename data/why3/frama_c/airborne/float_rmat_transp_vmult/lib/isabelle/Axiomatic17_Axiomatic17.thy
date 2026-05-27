theory Axiomatic17_Axiomatic17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S10_RealRMat_s_S10_RealRMat_s" "Compound_Compound" "S9_RealVect3_s_S9_RealVect3_s" "Why3STD.Cmath_Cmath" "Why3STD.Cfloat_Cfloat"
begin
definition l_l_rmat_of_floatrmat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s10_realrmat_s"
  where "l_l_rmat_of_floatrmat mflt_0 rmat_0 = (let a :: addr = shift rmat_0 (0 :: int) in s10_realrmat_s'mk (mflt_0 (shift a (0 :: int))) (mflt_0 (shift a (1 :: int))) (mflt_0 (shift a (2 :: int))) (mflt_0 (shift a (3 :: int))) (mflt_0 (shift a (4 :: int))) (mflt_0 (shift a (5 :: int))) (mflt_0 (shift a (6 :: int))) (mflt_0 (shift a (7 :: int))) (mflt_0 (shift a (8 :: int))))" for mflt_0 rmat_0
definition l_transpose :: "s10_realrmat_s \<Rightarrow> s10_realrmat_s"
  where "l_transpose rmat_0 = s10_realrmat_s'mk (f10_realrmat_s_a00 rmat_0) (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a20 rmat_0) (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a11 rmat_0) (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a22 rmat_0)" for rmat_0
definition l_mult_realrmat_realvect3 :: "s10_realrmat_s \<Rightarrow> s9_realvect3_s \<Rightarrow> s9_realvect3_s"
  where "l_mult_realrmat_realvect3 rm_0 v = (let r :: real = f9_realvect3_s_x v; r_1 :: real = f9_realvect3_s_y v; r_2 :: real = f9_realvect3_s_z v in s9_realvect3_s'mk (f10_realrmat_s_a00 rm_0 * r + f10_realrmat_s_a01 rm_0 * r_1 + f10_realrmat_s_a02 rm_0 * r_2) (f10_realrmat_s_a10 rm_0 * r + f10_realrmat_s_a11 rm_0 * r_1 + f10_realrmat_s_a12 rm_0 * r_2) (f10_realrmat_s_a20 rm_0 * r + f10_realrmat_s_a21 rm_0 * r_1 + f10_realrmat_s_a22 rm_0 * r_2))" for rm_0 v
end
