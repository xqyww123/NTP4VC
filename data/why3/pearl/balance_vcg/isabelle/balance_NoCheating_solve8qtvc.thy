theory balance_NoCheating_solve8qtvc
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
consts o1 :: "int \<Rightarrow> bool"
consts o2 :: "int \<Rightarrow> bool"
consts o3 :: "int \<Rightarrow> bool"
consts o4 :: "int \<Rightarrow> bool"
axiomatization where o1_def:   "o1 i = True \<longleftrightarrow> i = (3 :: int) \<or> i = (4 :: int) \<or> i = (5 :: int)"
  for i :: "int"
axiomatization where o2_def:   "o2 i = True \<longleftrightarrow> i = (0 :: int) \<or> i = (1 :: int) \<or> i = (2 :: int)"
  for i :: "int"
axiomatization where o3_def:   "o3 i = True \<longleftrightarrow> i = (7 :: int)"
  for i :: "int"
axiomatization where o4_def:   "o4 i = True \<longleftrightarrow> i = (6 :: int)"
  for i :: "int"
theorem solve8'vc:
  fixes counter1 :: "counter"
  fixes balls :: "int list"
  fixes lb :: "int"
  fixes w :: "int"
  assumes fact0: "v counter1 = (2 :: int)"
  assumes fact1: "spec balls (0 :: int) (8 :: int) lb w"
  shows "let o5 :: int \<Rightarrow> bool = o1; o6 :: int \<Rightarrow> bool = o2 in ((0 :: int) < v counter1 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (8 :: int) \<longrightarrow> \<not>o6 i = True \<or> \<not>o5 i = True)) \<and> (\<forall>(counter2 :: counter) (o7 :: outcome). (let left1 :: int = sum balls o6; right1 :: int = sum balls o5 in (case o7 of Left \<Rightarrow> right1 < left1 | Equal \<Rightarrow> left1 = right1 | Right \<Rightarrow> left1 < right1)) \<and> v counter2 = v counter1 - (1 :: int) \<longrightarrow> (case o7 of Right \<Rightarrow> (1 :: int) \<le> v counter2 \<and> spec balls (0 :: int) ((0 :: int) + (3 :: int)) lb w | Left \<Rightarrow> (1 :: int) \<le> v counter2 \<and> spec balls (3 :: int) ((3 :: int) + (3 :: int)) lb w | Equal \<Rightarrow> (let o8 :: int \<Rightarrow> bool = o3; o9 :: int \<Rightarrow> bool = o4 in ((0 :: int) < v counter2 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (8 :: int) \<longrightarrow> \<not>o9 i = True \<or> \<not>o8 i = True)) \<and> (\<forall>(counter3 :: counter) (o10 :: outcome). (let left1 :: int = sum balls o9; right1 :: int = sum balls o8 in (case o10 of Left \<Rightarrow> right1 < left1 | Equal \<Rightarrow> left1 = right1 | Right \<Rightarrow> left1 < right1)) \<and> v counter3 = v counter2 - (1 :: int) \<longrightarrow> (case o10 of Right \<Rightarrow> True | Left \<Rightarrow> True | Equal \<Rightarrow> False) \<and> (\<forall>(result :: int). (case o10 of Right \<Rightarrow> result = (6 :: int) | Left \<Rightarrow> result = (7 :: int) | Equal \<Rightarrow> False) \<longrightarrow> result = lb)))))"
  sorry
end
