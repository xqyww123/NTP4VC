theory linked_list_rev_Termination_set_cdrqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_NumOf"
begin
typedecl  loc
consts null :: "loc"
datatype  mem = mem'mk ("next": "loc \<Rightarrow> loc")
consts o1 :: "(loc \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> loc"
axiomatization where o1_def:   "o1 mem1 p v x = (if x = p then v else mem1 x)"
  for mem1 :: "loc \<Rightarrow> loc"
  and p :: "loc"
  and v :: "loc"
  and x :: "loc"
theorem set_cdr'vc:
  fixes p :: "loc"
  fixes mem1 :: "loc \<Rightarrow> loc"
  fixes v :: "loc"
  fixes mem2 :: "loc \<Rightarrow> loc"
  assumes fact0: "\<not>p = null"
  assumes fact1: "\<forall>(x :: loc). mem1 x = (if x = p then v else mem2 x)"
  shows "mem1 = mem2(p := v)"
  sorry
end
