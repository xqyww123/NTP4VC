theory Axiomatic18_Axiomatic18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "S11_RealQuat_s_S11_RealQuat_s" "Compound_Compound"
begin
definition l_l_quat_of_floatquat :: "(addr \<Rightarrow> real) \<Rightarrow> addr \<Rightarrow> s11_realquat_s"
  where "l_l_quat_of_floatquat mflt_0 q = s11_realquat_s'mk (mflt_0 (shift q (0 :: int))) (mflt_0 (shift q (1 :: int))) (mflt_0 (shift q (2 :: int))) (mflt_0 (shift q (3 :: int)))" for mflt_0 q
end
