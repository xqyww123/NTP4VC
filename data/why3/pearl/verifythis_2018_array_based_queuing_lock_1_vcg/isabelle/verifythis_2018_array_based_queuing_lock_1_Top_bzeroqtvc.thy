theory verifythis_2018_array_based_queuing_lock_1_Top_bzeroqtvc
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
theorem bzero'vc:
  shows "True"
  sorry
end
