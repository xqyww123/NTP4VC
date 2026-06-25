theory list_removal_Top_path_shortenqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  loc
typedecl  mem
consts null :: "loc"
consts head :: "loc"
consts entry :: "loc"
axiomatization where head_is_not_null:   "\<not>head = null"
axiomatization where entry_is_not_null:   "\<not>entry = null"
axiomatization where head_is_not_entry:   "\<not>head = entry"
consts list :: "(loc \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> int \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where list_def:   "if n = (0 :: int) then list mem1 x n y \<longleftrightarrow> x = y else list mem1 x n y \<longleftrightarrow> \<not>x = null \<and> list mem1 (mem1 x) (n - (1 :: int)) y"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and mem1 :: "loc \<Rightarrow> loc"
  and x :: "loc"
  and y :: "loc"
theorem path_shorten'vc:
  fixes mem1 :: "loc \<Rightarrow> loc"
  fixes x :: "loc"
  fixes n :: "int"
  fixes y :: "loc"
  assumes fact0: "list mem1 x n y"
  assumes fact1: "(0 :: int) < n"
  shows "list mem1 (mem1 x) (n - (1 :: int)) y"
  sorry
end
