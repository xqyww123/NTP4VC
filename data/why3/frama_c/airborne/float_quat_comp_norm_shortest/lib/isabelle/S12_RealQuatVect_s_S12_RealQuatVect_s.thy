theory S12_RealQuatVect_s_S12_RealQuatVect_s
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "S9_RealVect3_s_S9_RealVect3_s"
begin
datatype  s12_realquatvect_s = s12_realquatvect_s'mk (f12_realquatvect_s_scalar: "real") (f12_realquatvect_s_vect: "s9_realvect3_s")
definition eqs12_realquatvect_s :: "s12_realquatvect_s \<Rightarrow> s12_realquatvect_s \<Rightarrow> _"
  where "eqs12_realquatvect_s s s_1 \<longleftrightarrow> f12_realquatvect_s_scalar s_1 = f12_realquatvect_s_scalar s \<and> eqs9_realvect3_s (f12_realquatvect_s_vect s) (f12_realquatvect_s_vect s_1)" for s s_1
end
