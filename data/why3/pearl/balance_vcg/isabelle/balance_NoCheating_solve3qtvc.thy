theory balance_NoCheating_solve3qtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  outcome = Left | Equal | Right
typedecl  counter
consts v :: "counter \<Rightarrow> int"
typedecl  subset
definition sum :: "int list \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> int"
  where "sum balls s = (if s (0 :: int) = True then balls ! (0 :: nat) else (0 :: int)) + (if s (1 :: int) = True then balls ! (1 :: nat) else (0 :: int)) + (if s (2 :: int) = True then balls ! (2 :: nat) else (0 :: int)) + (if s (3 :: int) = True then balls ! (3 :: nat) else (0 :: int)) + (if s (4 :: int) = True then balls ! (4 :: nat) else (0 :: int)) + (if s (5 :: int) = True then balls ! (5 :: nat) else (0 :: int)) + (if s (6 :: int) = True then balls ! (6 :: nat) else (0 :: int)) + (if s (7 :: int) = True then balls ! (7 :: nat) else (0 :: int))" for balls s
definition spec :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "spec balls lo hi lb w \<longleftrightarrow> ((0 :: int) \<le> lo \<and> lo \<le> lb \<and> lb < hi \<and> hi \<le> int (length balls) \<and> int (length balls) = (8 :: int)) \<and> (\<forall>(i :: int). lo \<le> i \<and> i < hi \<longrightarrow> \<not>i = lb \<longrightarrow> balls ! nat i = w) \<and> balls ! nat lb < w" for balls lo hi lb w
consts o1 :: "int \<Rightarrow> int \<Rightarrow> bool"
consts o2 :: "int \<Rightarrow> int \<Rightarrow> bool"
axiomatization where o1_def:   "o1 lo i = True \<longleftrightarrow> i = lo + (1 :: int)"
  for lo :: "int"
  and i :: "int"
axiomatization where o2_def:   "o2 lo i = True \<longleftrightarrow> i = lo"
  for lo :: "int"
  and i :: "int"
theorem solve3'vc:
  fixes counter1 :: "counter"
  fixes balls :: "int list"
  fixes lo :: "int"
  fixes lb :: "int"
  fixes w :: "int"
  assumes fact0: "(1 :: int) \<le> v counter1"
  assumes fact1: "spec balls lo (lo + (3 :: int)) lb w"
  shows "let o3 :: int \<Rightarrow> bool = o1 lo; o4 :: int \<Rightarrow> bool = o2 lo in ((0 :: int) < v counter1 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (8 :: int) \<longrightarrow> \<not>o4 i = True \<or> \<not>o3 i = True)) \<and> (\<forall>(counter2 :: counter) (o5 :: outcome). (let left1 :: int = sum balls o4; right1 :: int = sum balls o3 in (case o5 of Left \<Rightarrow> right1 < left1 | Equal \<Rightarrow> left1 = right1 | Right \<Rightarrow> left1 < right1)) \<and> v counter2 = v counter1 - (1 :: int) \<longrightarrow> (case o5 of Right \<Rightarrow> True | Left \<Rightarrow> True | Equal \<Rightarrow> True) \<and> (\<forall>(result :: int). (case o5 of Right \<Rightarrow> result = lo | Left \<Rightarrow> result = lo + (1 :: int) | Equal \<Rightarrow> result = lo + (2 :: int)) \<longrightarrow> result = lb \<and> v counter2 = v counter1 - (1 :: int)))"
  sorry
end
