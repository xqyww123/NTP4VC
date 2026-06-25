theory esterel_Esterel_sqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded"
begin
theorem s'vc:
  shows "\<exists>(bv :: 64 word) (mdl :: int fset). \<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> ((0 \<le> i \<and> bit bv (nat i))) = True \<longleftrightarrow> i |\<in>| mdl"
  sorry
end
