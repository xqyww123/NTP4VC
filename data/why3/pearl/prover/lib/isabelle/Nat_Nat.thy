theory Nat_Nat
  imports "NTP4Verif.NTP4Verif"
begin
datatype  nat = ONat | SNat "nat"
fun nat_to_int :: "nat \<Rightarrow> int"
  where "nat_to_int ONat = (0 :: int)"
      | "nat_to_int (SNat n1) = (1 :: int) + nat_to_int n1" for n1
fun add_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "add_nat ONat n2 = n2" for n2
      | "add_nat (SNat n11) n2 = SNat (add_nat n11 n2)" for n11 n2
end
