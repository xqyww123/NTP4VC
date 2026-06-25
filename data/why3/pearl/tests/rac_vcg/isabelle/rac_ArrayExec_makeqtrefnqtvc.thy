theory rac_ArrayExec_makeqtrefnqtvc
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
consts make :: "int \<Rightarrow> 'a \<Rightarrow> 'a array"
axiomatization where make_spec'0:   "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> mixfix_lbrb (make n v) i = v"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and v :: "'a"
axiomatization where make_spec'1:   "length (make n v) = n"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and v :: "'a"
theorem make'refn'vc:
  fixes n :: "int"
  fixes result :: "'a array"
  fixes v :: "'a"
  assumes fact0: "(0 :: int) \<le> n"
  assumes fact1: "length result = n"
  assumes fact2: "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> elts result i = v"
  shows "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> mixfix_lbrb result i = v"
  and "length result = n"
  sorry
end
