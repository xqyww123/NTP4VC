theory verifythis_2018_array_based_queuing_lock_1_Top_bounded_int2qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts k :: "int"
axiomatization where k_def:   "(0 :: int) < k"
consts n :: "int"
axiomatization where n_def:   "(0 :: int) < n"
typedecl  bounded_int
consts bmodel :: "bounded_int \<Rightarrow> int"
axiomatization where bounded_int'invariant'0:   "(0 :: int) \<le> bmodel self"
  for self :: "bounded_int"
axiomatization where bounded_int'invariant'1:   "bmodel self < k * n"
  for self :: "bounded_int"
consts bzero :: "bounded_int"
axiomatization where bmodel_def:   "bmodel bzero = (0 :: int)"
theorem bounded_int2'vc:
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) < n"
  and "(0 :: int) \<le> (0 :: int) \<and> (0 :: int) < n \<longrightarrow> (0 :: int) = bmodel bzero cmod n"
  sorry
end
