theory rac_ArrayExec_makeqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a array = array'mk (length: "int") (elts: "int \<Rightarrow> 'a")
consts o1 :: "'a \<Rightarrow> int \<Rightarrow> 'a"
consts o2 :: "'a \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where o1_def:   "o1 v x = v"
  for v :: "'a"
  and x :: "int"
axiomatization where o2_def:   "o2 v x = v"
  for v :: "'a"
  and x :: "int"
theorem make'vc:
  fixes i :: "int"
  fixes n :: "int"
  fixes v :: "'a"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < n"
  shows "o2 v i = v"
  sorry
end
