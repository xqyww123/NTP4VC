theory string_search_Spec
  imports "NTP4Verif.NTP4Verif"
begin
definition matches1 :: "string \<Rightarrow> string \<Rightarrow> int \<Rightarrow> _"
  where "matches1 pat text p \<longleftrightarrow> ((0 :: int) \<le> p \<and> p \<le> int (length text) - int (length pat)) \<and> substring text p (int (length pat)) = pat" for pat "text" p
end
