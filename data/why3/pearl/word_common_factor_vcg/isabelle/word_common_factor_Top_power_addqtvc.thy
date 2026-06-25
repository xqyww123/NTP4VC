theory word_common_factor_Top_power_addqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
consts power :: "char list \<Rightarrow> int \<Rightarrow> char list"
axiomatization where power_def:   "if n = (0 :: int) then power w n = [] else power w n = w @ power w (n - (1 :: int))"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and w :: "char list"
theorem power_add'vc:
  fixes n1 :: "int"
  fixes n2 :: "int"
  fixes w :: "char list"
  assumes fact0: "(0 :: int) \<le> n1"
  assumes fact1: "(0 :: int) \<le> n2"
  shows "power w (n1 + n2) = power w n1 @ power w n2"
  sorry
end
