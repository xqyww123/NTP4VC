theory sumrange_ArraySum
  imports "NTP4Verif.NTP4Verif"
begin
consts sum :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where sum_def:   "if j \<le> i then sum a i j = (0 :: int) else sum a i j = a ! nat i + sum a (i + (1 :: int)) j"
 if "(0 :: int) \<le> i"
 and "i \<le> j"
 and "j \<le> int (length a)"
  for i :: "int"
  and j :: "int"
  and a :: "int list"
end
