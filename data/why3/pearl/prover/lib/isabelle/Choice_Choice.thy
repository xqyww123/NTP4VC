theory Choice_Choice
  imports "NTP4Verif.NTP4Verif"
begin
consts default :: "'a"
consts choice :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"
axiomatization where choice_behaviour:   "p (choice p) = True"
 if "p x = True"
  for p :: "'a \<Rightarrow> bool"
  and x :: "'a"
end
