theory verifythis_2018_array_based_queuing_lock_1_Top_bounded_intqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts k :: "int"
axiomatization where k_def:   "(0 :: int) < k"
consts n :: "int"
axiomatization where n_def:   "(0 :: int) < n"
theorem bounded_int'vc:
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) < k * n"
  sorry
end
