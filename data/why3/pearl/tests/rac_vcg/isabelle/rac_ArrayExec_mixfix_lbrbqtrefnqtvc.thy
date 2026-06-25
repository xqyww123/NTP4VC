theory rac_ArrayExec_mixfix_lbrbqtrefnqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a array = array'mk (length: "int") (elts: "int \<Rightarrow> 'a")
consts map_update :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where map_update_def:   "map_update f i x j = (if j = i then x else f j)"
  for f :: "int \<Rightarrow> 'a"
  and i :: "int"
  and x :: "'a"
  and j :: "int"
definition mixfix_lbrb' :: "'a array \<Rightarrow> int \<Rightarrow> 'a"
  where "mixfix_lbrb' a i = elts a i" for a i
definition mixfix_lbrb :: "'a array \<Rightarrow> int \<Rightarrow> 'a"
  where "mixfix_lbrb a i = elts a i" for a i
theorem mixfix_lbrb'refn'vc:
  fixes i :: "int"
  fixes a :: "'a array"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < length a"
  shows "elts a i = mixfix_lbrb a i"
  sorry
end
