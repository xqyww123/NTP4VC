theory hashtbl_test_TestHashtbl
  imports "NTP4Verif.NTP4Verif" "Why3STD.hashtbl_Hashtbl"
begin
consts k1 :: "key"
consts k2 :: "key"
consts k3 :: "key"
axiomatization where kdiff'0:   "\<not>k1 = k2"
axiomatization where kdiff'1:   "\<not>k1 = k3"
axiomatization where kdiff'2:   "\<not>k2 = k3"
end
