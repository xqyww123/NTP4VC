theory Axiomatic17_Axiomatic17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S10_RealRMat_s_S10_RealRMat_s" "Compound_Compound"
begin
definition l_l_rmat_of_floatrmat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s10_realrmat_s"
  where "l_l_rmat_of_floatrmat mflt_0 rmat_0 = (let a :: addr = shift rmat_0 (0 :: int) in s10_realrmat_s'mk (mflt_0 (shift a (0 :: int))) (mflt_0 (shift a (1 :: int))) (mflt_0 (shift a (2 :: int))) (mflt_0 (shift a (3 :: int))) (mflt_0 (shift a (4 :: int))) (mflt_0 (shift a (5 :: int))) (mflt_0 (shift a (6 :: int))) (mflt_0 (shift a (7 :: int))) (mflt_0 (shift a (8 :: int))))" for mflt_0 rmat_0
definition l_transpose :: "s10_realrmat_s \<Rightarrow> s10_realrmat_s"
  where "l_transpose rmat_0 = s10_realrmat_s'mk (f10_realrmat_s_a00 rmat_0) (f10_realrmat_s_a10 rmat_0) (f10_realrmat_s_a20 rmat_0) (f10_realrmat_s_a01 rmat_0) (f10_realrmat_s_a11 rmat_0) (f10_realrmat_s_a21 rmat_0) (f10_realrmat_s_a02 rmat_0) (f10_realrmat_s_a12 rmat_0) (f10_realrmat_s_a22 rmat_0)" for rmat_0
end
