theory rac_ArrayExec_mixfix_lbrblsmnqtrefnqtvc
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
consts mixfix_lblsmnrb :: "'a array \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> 'a array"
axiomatization where mixfix_lblsmnrb'spec'0:   "length (mixfix_lblsmnrb a i v) = length a"
  for a :: "'a array"
  and i :: "int"
  and v :: "'a"
axiomatization where mixfix_lblsmnrb'spec:   "elts (mixfix_lblsmnrb a i v) = (elts a)(i := v)"
  for a :: "'a array"
  and i :: "int"
  and v :: "'a"
theorem mixfix_lbrblsmn'refn'vc:
  fixes i :: "int"
  fixes a :: "'a array"
  fixes a1 :: "'a array"
  fixes v :: "'a"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < length a"
  assumes fact2: "length a1 = length a"
  shows "elts a1 = (elts a)(i := v)"
  and "a1 = mixfix_lblsmnrb a i v"
  sorry
end
