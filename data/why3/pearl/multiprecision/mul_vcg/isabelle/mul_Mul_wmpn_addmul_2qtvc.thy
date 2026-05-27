theory mul_Mul_wmpn_addmul_2qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.add_Add"
begin
theorem wmpn_addmul_2'vc:
  fixes sz :: "32 word"
  fixes x :: "64 word ptr"
  fixes y :: "64 word ptr"
  fixes r :: "64 word ptr"
  assumes fact0: "(0 :: int) < sint sz"
  assumes fact1: "valid x (sint sz)"
  assumes fact2: "valid y (2 :: int)"
  assumes fact3: "valid r (sint sz + (2 :: int))"
  assumes fact4: "writable r = True"
  shows "c_C.min y \<le> offset y"
  and "offset y < c_C.max y"
  and "valid x (sint sz)"
  and "valid r (sint sz)"
  and "writable r = True"
  and "\<forall>(r1 :: 64 word ptr). length (data r1) = length (data r) \<and> offset r1 = offset r \<and> c_C.min r1 = c_C.min r \<and> c_C.max r1 = c_C.max r \<and> writable r1 = writable r \<and> zone1 r1 = zone1 r \<longrightarrow> (\<forall>(rn :: 64 word). value r1 (sint sz) + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sz * uint rn = value r (sint sz) + value x (sint sz) * uint (pelts y (offset y)) \<and> (\<forall>(j :: int). j < offset r1 \<or> offset r1 + sint sz \<le> j \<longrightarrow> pelts r1 j = pelts r j) \<longrightarrow> ((c_C.min r1 \<le> offset r1 + sint sz \<and> offset r1 + sint sz < c_C.max r1) \<and> writable r1 = True) \<and> (\<forall>(r2 :: 64 word ptr). length (data r2) = length (data r1) \<and> offset r2 = offset r1 \<and> c_C.min r2 = c_C.min r1 \<and> c_C.max r2 = c_C.max r1 \<and> writable r2 = writable r1 \<and> zone1 r2 = zone1 r1 \<longrightarrow> pelts r2 = (pelts r1)(offset r2 + sint sz := rn) \<and> pelts r2 (offset r2 + sint sz) = rn \<longrightarrow> (c_C.min r2 \<le> offset r2 + (1 :: int) \<and> offset r2 + (1 :: int) \<le> c_C.max r2) \<and> (\<forall>(r11 :: 64 word ptr). offset r11 = offset r2 + (1 :: int) \<and> plength r11 = plength r2 \<and> pelts r11 = pelts r2 \<and> data r11 = data r2 \<and> c_C.min r11 = c_C.min r2 \<and> c_C.max r11 = c_C.max r2 \<and> zone1 r11 = zone1 r2 \<and> writable r11 = writable r2 \<longrightarrow> (c_C.min y \<le> offset y + (1 :: int) \<and> offset y + (1 :: int) < c_C.max y) \<and> (valid x (sint sz) \<and> valid r11 (sint sz) \<and> writable r11 = True) \<and> (\<forall>(r12 :: 64 word ptr) (r3 :: 64 word ptr). data r12 = data r3 \<and> length (data r3) = length (data r11) \<and> offset r12 = offset r11 \<and> c_C.min r12 = c_C.min r11 \<and> c_C.max r12 = c_C.max r11 \<and> writable r12 = writable r11 \<and> zone1 r12 = zone1 r11 \<longrightarrow> length (data r3) = length (data r2) \<and> offset r3 = offset r2 \<and> c_C.min r3 = c_C.min r2 \<and> c_C.max r3 = c_C.max r2 \<and> writable r3 = writable r2 \<and> zone1 r3 = zone1 r2 \<longrightarrow> (\<forall>(c :: 64 word). value r12 (sint sz) + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sz * uint c = value r11 (sint sz) + value x (sint sz) * uint (pelts y (offset y + (1 :: int))) \<and> (\<forall>(j :: int). j < offset r12 \<or> offset r12 + sint sz \<le> j \<longrightarrow> pelts r12 j = pelts r11 j) \<longrightarrow> value r3 (sint sz + (1 :: int)) + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (sint sz + (1 :: int)) * uint c = value r (sint sz) + value x (sint sz) * value y (2 :: int) \<and> (\<forall>(j :: int). j < offset r3 \<or> offset r3 + sint sz + (1 :: int) \<le> j \<longrightarrow> pelts r3 j = pelts r j))))))"
  sorry
end
