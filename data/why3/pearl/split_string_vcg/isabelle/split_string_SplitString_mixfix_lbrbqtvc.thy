theory split_string_SplitString_mixfix_lbrbqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
typedecl  string'
consts concat :: "char list list \<Rightarrow> char \<Rightarrow> char list"
axiomatization where concat_def:   "if int (length ss) = (1 :: int) then concat ss sep = ss ! (0 :: nat) else concat ss sep = concat (drop (0 :: nat) (take (nat (int (length ss) - (1 :: int)) - (0 :: nat)) ss)) sep @ Cons sep (ss ! nat (int (length ss) - (1 :: int)))"
 if "(1 :: int) \<le> int (length ss)"
  for ss :: "char list list"
  and sep :: "char"
definition notin :: "char \<Rightarrow> char list \<Rightarrow> _"
  where "notin sep s \<longleftrightarrow> \<not>sep \<in> set s" for sep s
theorem mixfix_lbrb'vc:
  shows "True"
  sorry
end
