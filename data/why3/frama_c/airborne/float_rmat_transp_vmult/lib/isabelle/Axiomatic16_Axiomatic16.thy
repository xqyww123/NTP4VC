theory Axiomatic16_Axiomatic16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S9_RealVect3_s_S9_RealVect3_s" "Compound_Compound"
begin
definition l_l_vect_of_floatvect3 :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s9_realvect3_s"
  where "l_l_vect_of_floatvect3 mflt_0 v = s9_realvect3_s'mk (mflt_0 (shift v (0 :: int))) (mflt_0 (shift v (1 :: int))) (mflt_0 (shift v (2 :: int)))" for mflt_0 v
end
