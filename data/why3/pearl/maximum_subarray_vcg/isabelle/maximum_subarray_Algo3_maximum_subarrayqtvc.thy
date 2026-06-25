theory maximum_subarray_Algo3_maximum_subarrayqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_Sum" "./maximum_subarray_Spec"
begin
theorem maximum_subarray'vc:
  fixes a :: "int list"
  shows "let o1 :: int = int (length a) in ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> o1 \<and> o1 \<le> int (length a)) \<and> (\<forall>(hi :: int) (lo :: int). ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> o1) \<and> (\<forall>(l' :: int) (h' :: int). (0 :: int) \<le> l' \<and> l' \<le> h' \<and> h' \<le> o1 \<longrightarrow> sum_list (take (nat h' - nat l') (drop (nat l') a)) \<le> sum_list (take (nat hi - nat lo) (drop (nat lo) a))) \<longrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> hi \<and> hi \<le> int (length a)) \<and> maxsub a (sum_list (take (nat hi - nat lo) (drop (nat lo) a))))"
  sorry
end
