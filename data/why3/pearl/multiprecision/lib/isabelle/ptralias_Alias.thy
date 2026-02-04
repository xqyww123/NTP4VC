theory ptralias_Alias
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq"
begin
typedecl  mem
consts zr :: "mem \<Rightarrow> zone"
consts zx :: "mem \<Rightarrow> zone"
consts zy :: "mem \<Rightarrow> zone"
consts mr :: "mem \<Rightarrow> 32 word"
consts mx :: "mem \<Rightarrow> 32 word"
consts my :: "mem \<Rightarrow> 32 word"
consts lr :: "mem \<Rightarrow> 32 word"
consts lx :: "mem \<Rightarrow> 32 word"
consts ly :: "mem \<Rightarrow> 32 word"
consts ok :: "mem \<Rightarrow> bool"
definition identical :: "64 word ptr \<Rightarrow> 64 word ptr \<Rightarrow> _"
  where "identical p1 p2 \<longleftrightarrow> data p1 = data p2 \<and> offset p1 = offset p2 \<and> c_C.min p1 = c_C.min p2 \<and> c_C.max p1 = c_C.max p2 \<and> zone1 p1 = zone1 p2" for p1 p2
end
