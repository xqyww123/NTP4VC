theory NTP4Verif
  imports Complex_Main Automation_Base.Automation_Base Word_Lib.Word_Lemmas Minilang.Minilang
          "HOL-Library.Finite_Map" "HOL-Library.FSet" "HOL-Library.Multiset_Order"
          "HOL-Number_Theory.Prime_Powers" "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
          "HOL-Library.Sublist" "List-Index.List_Index"
          "HOL-Combinatorics.List_Permutation"
          (* IEEE_Floating_Point.Conversion_IEEE_Float IEEE_Floating_Point.FP64 *)
begin

setup \<open>Context.theory_map (Default_Num_Typ.set NONE)\<close>

declare [[coercion_enabled = false]]

section \<open> Builtins \<close>

abbreviation is_Nil where \<open>is_Nil l \<equiv> l = []\<close>

abbreviation length_i where "length_i l \<equiv> Int.int (List.length l)"

abbreviation drop_i where "drop_i n l \<equiv> List.drop (Int.nat n) l"

abbreviation take_i where "take_i n l \<equiv> List.take (Int.nat n) l"

abbreviation (input) is_None where "is_None x \<equiv> x = None"


abbreviation (input) nthi (infixl "!\<^sub>i" 100) where \<open>nthi l x \<equiv> nth l (Int.nat x)\<close>

abbreviation (input) nth_opt (infixl "!\<^sub>i''" 100)
  where \<open>nth_opt l x \<equiv> if 0 \<le> x \<and> x < length_i l then Some (nth l (Int.nat x)) else None\<close>

abbreviation (input) hd_opt
  where "hd_opt l \<equiv> if l = [] then None else Some (hd l)"

abbreviation (input) tl_opt
  where "tl_opt l \<equiv> if l = [] then None else Some (tl l)"

abbreviation (input) rev_append where "rev_append r s \<equiv> rev r @ s"

abbreviation (input) create_list where "create_list n f \<equiv> map (\<lambda>x. f (int x)) [0 ..< nat n]"
abbreviation (input) replicate_i where "replicate_i n x \<equiv> replicate (nat n) x"

abbreviation (input) slice where "slice l i j \<equiv> drop i (take (j - i) l)" 
abbreviation (input) slice_i where "slice_i l i j \<equiv> drop (nat i) (take (nat j - nat i) l)" 

abbreviation (input) fset_is_empty where "fset_is_empty s \<equiv> s = fempty"
abbreviation (input) set_is_empty where "set_is_empty s \<equiv> s = {}"

abbreviation (input) fset_remove where "fset_remove x s \<equiv> s |-| {| x |}"
abbreviation (input) set_remove where "set_remove x A \<equiv> A - {x}"

abbreviation (input) fset_pick where "fset_pick s \<equiv> (@x. x |\<in>| s)"

abbreviation (input) fset_disjoint where "fset_disjoint A B \<equiv> A |\<inter>| B = fempty"

abbreviation (input) fset_filter where "fset_filter s f \<equiv> FSet.ffilter f s"
abbreviation (input) set_filter where "set_filter A P \<equiv> {a \<in> A. P a}"

abbreviation (input) fcard_i where "fcard_i x \<equiv> int (fcard x)"

abbreviation (input) fm_contents where "fm_contents f k \<equiv> the (fmlookup f k)"
abbreviation (input) fm_find where "fm_find k m \<equiv> fm_contents m k"
abbreviation (input) fm_mem where "fm_mem k m \<equiv> k |\<in>| fmdom m"
abbreviation (input) fm_mapsto where "fm_mapsto k v m \<equiv> fmlookup m k = Some v"
abbreviation (input) fm_is_empty where "fm_is_empty m \<equiv> fset_is_empty (fmdom m)"
abbreviation (input) fm_size where "fm_size m \<equiv> fcard (fset_of_fmap m)"

context
  includes fmap.lifting
begin

lift_definition fm_of_fset :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a,'b) fmap"
  is \<open>\<lambda>s f k. if k |\<in>| s then Some (f k) else None\<close>
  unfolding dom_def
  by transfer auto

lemma fmlookup_fm_of_fset[simp]:
  "fmlookup (fm_of_fset A f) x = (if x |\<in>| A then Some (f x) else None)"
  by (transfer, auto)


lemma fmdom_fm_of_fset[simp]: "fmdom (fm_of_fset A f) = A"
  unfolding fmdom_def
  by (transfer, auto,
      smt (verit, ccfv_threshold) domIff fset_inverse option.distinct(1) set_eqI,
      smt (verit, best) domI domIff fset_inverse set_eqI)
end

abbreviation (input) int_power :: "'a::power \<Rightarrow> int \<Rightarrow> 'a" (infixr "^\<^sub>i" 80)
  where "(x::'a::power) ^\<^sub>i i \<equiv> x ^ nat i"

abbreviation (input) power2 :: "int \<Rightarrow> int" where "power2 n \<equiv> 2 ^ nat n"

abbreviation (input) bag_count_i :: "'a \<Rightarrow> 'a multiset \<Rightarrow> int" where
  "bag_count_i x bag \<equiv> int (multiset.count bag x)"

abbreviation (input) bag_size :: "'a multiset \<Rightarrow> int" where
  "bag_size bag \<equiv> int (size bag)"

abbreviation (input) bag_pick where "bag_pick s \<equiv> (@x. x \<in># s)"

lemma bag_pick:
  fixes b :: "'a multiset"
  assumes fact0: "b \<noteq> {#}"
  shows "bag_pick b \<in># b"
  by (simp add: fact0 some_in_eq)

abbreviation Ico_fset_int :: "int \<Rightarrow> int \<Rightarrow> int fset"
  where "Ico_fset_int i j \<equiv> fset_of_list [i..(j-1)]"

definition list_exchange :: "'a list \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "list_exchange a1 a2 i j \<longleftrightarrow> a1 = a2[nat i := a1 ! nat j, nat j := a1 ! nat i]" for a1 a2 i j

abbreviation permut_sub :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> _"
  where "permut_sub a1 a2 l u
    \<equiv> length a1 = length a2 \<and> (0 \<le> l \<and> l \<le> length a1) \<and> (0 \<le> u \<and> u \<le> length a1)
    \<and> slice a1 l u <~~> slice a2 l u" for a1 a2 l u

abbreviation permut_sub' :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> _"
  where "permut_sub' a1 a2 l u
    \<equiv> length a1 = length a2
    \<and> slice a1 0 l = slice a2 0 l
    \<and> slice a1 u (length a1) = slice a2 u (length a1)
    \<and> slice a1 l u <~~> slice a2 l u" for a1 a2 l u

abbreviation list_mem' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where "list_mem' eq x l \<equiv> list_all (eq x) l" for eq x l

abbreviation trunc_toward_zero :: "real \<Rightarrow> int" where
    "trunc_toward_zero x \<equiv> (if x \<ge> 0 then \<lfloor>x\<rfloor> else \<lceil>x\<rceil>)"

(* abbreviation rounding_mode_to_nearest
  where "rounding_mode_to_nearest m \<equiv> m = RNE \<or> m = RNA" for m *)

section \<open> Words \<close>

abbreviation (input) take_bit_i where "take_bit_i (x::'a::len word) i \<equiv> take_bit (nat i) x \<noteq> 0"
abbreviation (input) take_bit_bv where "take_bit_bv (x::'a::len word) i \<equiv> take_bit (unat i) x \<noteq> 0"

abbreviation word_sli (infixl \<open><<\<^sub>i\<close> 55)
  where "(x::'a::len word) <<\<^sub>i n \<equiv> x << nat n"
abbreviation word_sri (infixl \<open>>>\<^sub>i\<close> 55)
  where "(x::'a::len word) >>\<^sub>i n \<equiv> x >> nat n"

abbreviation (input) word_sl_bv (infixl \<open><<\<^sub>b\<close> 55)
  where "(x::'a::len word) <<\<^sub>b n \<equiv> x << unat n"
abbreviation (input) word_sr_bv (infixl \<open>>>\<^sub>b\<close> 55)
  where "(x::'a::len word) >>\<^sub>b n \<equiv> x >> unat n"

abbreviation (input) w8_of_int :: "int \<Rightarrow> 8 word" where "w8_of_int \<equiv> of_int"
abbreviation (input) w16_of_int :: "int \<Rightarrow> 16 word" where "w16_of_int \<equiv> of_int"
abbreviation (input) w32_of_int :: "int \<Rightarrow> 32 word" where "w32_of_int \<equiv> of_int"
abbreviation (input) w64_of_int :: "int \<Rightarrow> 64 word" where "w64_of_int \<equiv> of_int"
abbreviation (input) w128_of_int :: "int \<Rightarrow> 128 word" where "w128_of_int \<equiv> of_int"
abbreviation (input) w256_of_int :: "int \<Rightarrow> 256 word" where "w256_of_int \<equiv> of_int"
abbreviation (input) uchar_of_char :: "char \<Rightarrow> 8 word" where "uchar_of_char \<equiv> of_char"
abbreviation (input) char_of_uchar :: "8 word \<Rightarrow> char" where "char_of_uchar x \<equiv> char_of (unat x)"

abbreviation (input) u8_to_u32 :: "8 word \<Rightarrow> 32 word" where \<open>u8_to_u32 \<equiv> ucast\<close>
abbreviation (input) s8_to_s32 :: "8 word \<Rightarrow> 32 word" where \<open>s8_to_s32 \<equiv> scast\<close>
abbreviation (input) u32_to_u8 :: "32 word \<Rightarrow> 8 word" where \<open>u32_to_u8 \<equiv> ucast\<close>
abbreviation (input) u8_to_u128 :: "8 word \<Rightarrow> 128 word" where \<open>u8_to_u128 \<equiv> ucast\<close>
abbreviation (input) s8_to_s128 :: "8 word \<Rightarrow> 128 word" where \<open>s8_to_s128 \<equiv> scast\<close>
abbreviation (input) u128_to_u8 :: "128 word \<Rightarrow> 8 word" where \<open>u128_to_u8 \<equiv> ucast\<close>
abbreviation (input) u32_to_u64 :: "32 word \<Rightarrow> 64 word" where \<open>u32_to_u64 \<equiv> ucast\<close>
abbreviation (input) s32_to_s64 :: "32 word \<Rightarrow> 64 word" where \<open>s32_to_s64 \<equiv> scast\<close>
abbreviation (input) u64_to_u32 :: "64 word \<Rightarrow> 32 word" where \<open>u64_to_u32 \<equiv> ucast\<close>
abbreviation (input) u32_to_u128 :: "32 word \<Rightarrow> 128 word" where \<open>u32_to_u128 \<equiv> ucast\<close>
abbreviation (input) s32_to_s128 :: "32 word \<Rightarrow> 128 word" where \<open>s32_to_s128 \<equiv> scast\<close>
abbreviation (input) u128_to_u32 :: "128 word \<Rightarrow> 32 word" where \<open>u128_to_u32 \<equiv> ucast\<close>
abbreviation (input) u64_to_u128 :: "64 word \<Rightarrow> 128 word" where \<open>u64_to_u128 \<equiv> ucast\<close>
abbreviation (input) s64_to_s128 :: "64 word \<Rightarrow> 128 word" where \<open>s64_to_s128 \<equiv> scast\<close>
abbreviation (input) u128_to_u64 :: "128 word \<Rightarrow> 64 word" where \<open>u128_to_u64 \<equiv> ucast\<close>

abbreviation (input) bv_eq_sub :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "bv_eq_sub a b i n \<equiv> take_bit (nat n) (drop_bit (LENGTH('a) - nat n - nat i) a) = take_bit (nat n) (drop_bit (LENGTH('a) - nat n - nat i) b)"

abbreviation (input) bv_eq_sub_bv :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "bv_eq_sub_bv a b i n \<equiv> take_bit (unat n) (drop_bit (LENGTH('a) - unat n - unat i) a) = take_bit (unat n) (drop_bit (LENGTH('a) - unat n - unat i) b)"

abbreviation (input) "w8_size_i \<equiv> (8 :: int)"
abbreviation (input) "w16_size_i \<equiv> (16 :: int)"
abbreviation (input) "w32_size_i \<equiv> (32 :: int)"
abbreviation (input) "w64_size_i \<equiv> (64 :: int)"
abbreviation (input) "w128_size_i \<equiv> (128 :: int)"
abbreviation (input) "w256_size_i \<equiv> (256 :: int)"

abbreviation (input) "w8_size_bv \<equiv> (8 :: 8 word)"
abbreviation (input) "w16_size_bv \<equiv> (16 :: 16 word)"
abbreviation (input) "w32_size_bv \<equiv> (32 :: 32 word)"
abbreviation (input) "w64_size_bv \<equiv> (64 :: 64 word)"
abbreviation (input) "w128_size_bv \<equiv> (128 :: 128 word)"
abbreviation (input) "w256_size_bv \<equiv> (256 :: 256 word)"

abbreviation (input) is_msb_set :: \<open>'a::len word \<Rightarrow> bool\<close>
  where \<open>is_msb_set x \<equiv> 2^LENGTH('a) < 2 * unat x\<close>

syntax
  word_sge :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"      ("(_/ \<ge>s _)"  [51, 51] 50)
  word_sgrater :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"  ("(_/ >s _)"  [51, 51] 50)

translations
  "a \<ge>s b" => "b \<le>s a"
  "a >s b" => "b <s a"

abbreviation (input) word_rotl_i  where "word_rotl_i  x n \<equiv> word_rotl (nat  n) x"
abbreviation (input) word_rotl_bv where "word_rotl_bv x n \<equiv> word_rotl (unat n) x"
abbreviation (input) word_rotr_i  where "word_rotr_i  x n \<equiv> word_rotr (nat  n) x"
abbreviation (input) word_rotr_bv where "word_rotr_bv x n \<equiv> word_rotr (unat n) x"
abbreviation (input) word_ashr_i  (infixl \<open>>>>\<^sub>i\<close> 55) where "word_ashr_i  x n \<equiv> x >>> nat n"
abbreviation (input) word_ashr_bv (infixl \<open>>>>\<^sub>b\<close> 55) where "word_ashr_bv x n \<equiv> x >>> unat n"

abbreviation (input) int'16_max :: "16 word" where "int'16_max \<equiv> 32767"
abbreviation (input) int'16_min :: "16 word" where "int'16_min \<equiv> -32768"
abbreviation (input) int'31_max :: "31 word" where "int'31_max \<equiv> 1073741823"
abbreviation (input) int'31_min :: "31 word" where "int'31_min \<equiv> -1073741824"
abbreviation (input) int'32_max :: "32 word" where "int'32_max \<equiv> 2147483647"
abbreviation (input) int'32_min :: "32 word" where "int'32_min \<equiv> -2147483648"
abbreviation (input) int'63_max :: "63 word" where "int'63_max \<equiv> 4611686018427387903"
abbreviation (input) int'63_min :: "63 word" where "int'63_min \<equiv> -4611686018427387904"
abbreviation (input) int'64_max :: "64 word" where "int'64_max \<equiv> 9223372036854775807"
abbreviation (input) int'64_min :: "64 word" where "int'64_min \<equiv> -9223372036854775808"
abbreviation (input) uint'16_max :: "16 word" where "uint'16_max \<equiv> 65535"
abbreviation (input) uint'16_min :: "16 word" where "uint'16_min \<equiv> 0"
abbreviation (input) uint'31_max :: "31 word" where "uint'31_max \<equiv> 2147483647"
abbreviation (input) uint'31_min :: "31 word" where "uint'31_min \<equiv> 0"
abbreviation (input) uint'32_max :: "32 word" where "uint'32_max \<equiv> 4294967295"
abbreviation (input) uint'32_min :: "32 word" where "uint'32_min \<equiv> 0"
abbreviation (input) uint'63_max :: "63 word" where "uint'63_max \<equiv> 9223372036854775807"
abbreviation (input) uint'63_min :: "63 word" where "uint'63_min \<equiv> 0"
abbreviation (input) uint'64_max :: "64 word" where "uint'64_max \<equiv> 18446744073709551615"
abbreviation (input) uint'64_min :: "64 word" where "uint'64_min \<equiv> 0"

abbreviation (input) int'16_in_bounds :: "int \<Rightarrow> bool" where "int'16_in_bounds x \<equiv> sint int'16_min \<le> x \<and> x \<le> sint int'16_max"
abbreviation (input) int'31_in_bounds :: "int \<Rightarrow> bool" where "int'31_in_bounds x \<equiv> sint int'31_min \<le> x \<and> x \<le> sint int'31_max"
abbreviation (input) int'32_in_bounds :: "int \<Rightarrow> bool" where "int'32_in_bounds x \<equiv> sint int'32_min \<le> x \<and> x \<le> sint int'32_max"
abbreviation (input) int'63_in_bounds :: "int \<Rightarrow> bool" where "int'63_in_bounds x \<equiv> sint int'63_min \<le> x \<and> x \<le> sint int'63_max"
abbreviation (input) int'64_in_bounds :: "int \<Rightarrow> bool" where "int'64_in_bounds x \<equiv> sint int'64_min \<le> x \<and> x \<le> sint int'64_max"
abbreviation (input) uint'8_in_bounds :: "int \<Rightarrow> bool" where "uint'8_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> 256"
abbreviation (input) uint'16_in_bounds :: "int \<Rightarrow> bool" where "uint'16_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> uint int'16_max"
abbreviation (input) uint'31_in_bounds :: "int \<Rightarrow> bool" where "uint'31_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> uint int'31_max"
abbreviation (input) uint'32_in_bounds :: "int \<Rightarrow> bool" where "uint'32_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> uint int'32_max"
abbreviation (input) uint'63_in_bounds :: "int \<Rightarrow> bool" where "uint'63_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> uint int'63_max"
abbreviation (input) uint'64_in_bounds :: "int \<Rightarrow> bool" where "uint'64_in_bounds x \<equiv> 0 \<le> x \<and> x \<le> uint int'64_max"


lemma int'16_max [simp]: "sint (x::16 word) \<le> sint int'16_max"
  using sint_less[of x, simplified]
  by auto

lemma int'31_max [simp]: "sint (x::31 word) \<le> sint int'31_max"
  using sint_less[of x, simplified]
  by auto

lemma int'32_max [simp]: "sint (x::32 word) \<le> sint int'32_max"
  using sint_less[of x, simplified]
  by auto

lemma int'63_max [simp]: "sint (x::63 word) \<le> sint int'63_max"
  using sint_less[of x, simplified]
  by auto

lemma int'64_max [simp]: "sint (x::64 word) \<le> sint int'64_max"
  using sint_less[of x, simplified]
  by auto

lemma int'16_min [simp]: "sint int'16_min \<le> sint (x::16 word)"
  using sint_greater_eq[of x, simplified]
  by simp

lemma int'31_min [simp]: "sint int'31_min \<le> sint (x::31 word)"
  using sint_greater_eq[of x, simplified]
  by simp

lemma int'32_min [simp]: "sint int'32_min \<le> sint (x::32 word)"
  using sint_greater_eq[of x, simplified]
  by auto

lemma int'63_min [simp]: "sint int'63_min \<le> sint (x::63 word)"
  using sint_greater_eq[of x, simplified]
  by auto

lemma int'64_min [simp]: "sint int'64_min \<le> sint (x::64 word)"
  using sint_greater_eq[of x, simplified]
  by auto

lemmas int'16_max'[simp] = sint_less[where 'a = 16, simplified]
lemmas int'31_max'[simp] = sint_less[where 'a = 31, simplified]
lemmas int'32_max'[simp] = sint_less[where 'a = 32, simplified]
lemmas int'63_max'[simp] = sint_less[where 'a = 63, simplified]
lemmas int'64_max'[simp] = sint_less[where 'a = 64, simplified]
lemmas int'16_min'[simp] = sint_greater_eq[where 'a = 16, simplified]
lemmas int'31_min'[simp] = sint_greater_eq[where 'a = 31, simplified]
lemmas int'32_min'[simp] = sint_greater_eq[where 'a = 32, simplified]
lemmas int'63_min'[simp] = sint_greater_eq[where 'a = 63, simplified]
lemmas int'64_min'[simp] = sint_greater_eq[where 'a = 64, simplified]

lemma uint'16_max [simp]: "uint (x::16 word) \<le> uint uint'16_max"
  using uint_range'[of x, simplified]
  by auto

lemma uint'31_max [simp]: "uint (x::31 word) \<le> uint uint'31_max"
  using uint_range'[of x, simplified]
  by auto

lemma uint'32_max [simp]: "uint (x::32 word) \<le> uint uint'32_max"
  using uint_range'[of x, simplified]
  by auto

lemma uint'63_max [simp]: "uint (x::63 word) \<le> uint uint'63_max"
  using uint_range'[of x, simplified]
  by auto

lemma uint'64_max [simp]: "uint (x::64 word) \<le> uint uint'64_max"
  using uint_range'[of x, simplified]
  by auto

lemmas uint'16_max'[simp] = uint_range'[where 'a = 16, simplified]
lemmas uint'31_max'[simp] = uint_range'[where 'a = 31, simplified]
lemmas uint'32_max'[simp] = uint_range'[where 'a = 32, simplified]
lemmas uint'63_max'[simp] = uint_range'[where 'a = 63, simplified]
lemmas uint'64_max'[simp] = uint_range'[where 'a = 64, simplified]

subsection "Machine Array"

typedecl 'a array31
typedecl 'a array32
typedecl 'a array63

consts array31_elts :: "'a array31 \<Rightarrow> int \<Rightarrow> 'a"
consts array32_elts :: "'a array32 \<Rightarrow> int \<Rightarrow> 'a"
consts array63_elts :: "'a array63 \<Rightarrow> 'a list"

abbreviation (input) array63_nth where "array63_nth a i \<equiv> array63_elts a !\<^sub>i i"

consts array31_length :: "'a array31 \<Rightarrow> 31 word"
consts array32_length :: "'a array32 \<Rightarrow> 32 word"
consts array63_length :: "'a array63 \<Rightarrow> 63 word"

axiomatization where
      array31_length: "0 \<le> sint (array31_length x1)"
  and array32_length: "0 \<le> sint (array32_length x2)"
  and array63_length: "0 \<le> sint (array63_length x3)"
  and array64_length: "0 \<le> sint (array64_length x4)"

lemma sint_ge_0_uint_lt_half: "0 \<le> sint (x::'a::len word) \<Longrightarrow> uint x < 2^(LENGTH('a) - 1)"
  by (metis not_less sint_eq_uint sint_lt word_msb_sint)

lemma sint_ge_0_uint_lt_half_31: "0 \<le> sint (x::31 word) \<Longrightarrow> x \<le> int'31_max"
  using sint_ge_0_uint_lt_half[of x]
  by (simp add: word_le_def)

lemma sint_ge_0_uint_lt_half_32: "0 \<le> sint (x::32 word) \<Longrightarrow> x \<le> int'32_max"
  using sint_ge_0_uint_lt_half[of x]
  by (simp add: word_le_def)

lemma sint_ge_0_uint_lt_half_63: "0 \<le> sint (x::63 word) \<Longrightarrow> x \<le> int'63_max"
  using sint_ge_0_uint_lt_half[of x]
  by (simp add: word_le_def)

lemma sint_ge_0_uint_lt_half_64: "0 \<le> sint (x::64 word) \<Longrightarrow> x \<le> int'64_max"
  using sint_ge_0_uint_lt_half[of x]
  by (simp add: word_le_def)

lemma array31_length_range: "array31_length x1 \<le> int'31_max"
  using sint_ge_0_uint_lt_half_31 array31_length by blast

lemma array32_length_range: "array32_length x1 \<le> int'32_max"
  using sint_ge_0_uint_lt_half_32 array32_length by blast

lemma array63_length_range: "array63_length x1 \<le> int'63_max"
  using sint_ge_0_uint_lt_half_63 array63_length by blast


section \<open> Map Occurrence \<close>

definition map_occ where \<open>map_occ v m (l::int) u = card {n. l \<le> n \<and> n < u \<and> m n = v }\<close>
abbreviation (input) map_occ_i where \<open>map_occ_i v m l u \<equiv> int (map_occ v m l u)\<close>

lemma map_occ_empty:
        fixes u :: \<open>int\<close>
  fixes l :: \<open>int\<close>
  fixes v :: \<open>'a\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  assumes fact0: \<open>u \<le> l\<close>
  shows \<open>map_occ v m l u = 0\<close>
  unfolding map_occ_def
  using card_eq_0_iff fact0 by fastforce

lemma map_occ_right_no_add:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>l < u\<close>
  assumes fact1: \<open>\<not>m (u - 1) = v\<close>
  shows \<open>map_occ v m l u = map_occ v m l (u - 1)\<close>
  unfolding map_occ_def
  by (metis fact1 nless_le zle_diff1_eq)

lemma map_occ_right_add:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>l < u\<close>
  assumes fact1: \<open>m (u - 1) = v\<close>
  shows \<open>map_occ v m l u = 1 + map_occ v m l (u - 1)\<close>
  unfolding map_occ_def
proof -
  have t: "{n. l \<le> n \<and> n < u \<and> m n = v} = {u-1} \<union> {n. l \<le> n \<and> n < u - 1 \<and> m n = v}"
    unfolding set_eq_iff
    by (auto simp add: fact0 fact1)
  have t3: "finite {n. l \<le> n \<and> n < u - 1 \<and> m n = v}"
    using finite_Collect_conjI by force
  show "card {n. l \<le> n \<and> n < u \<and> m n = v} = 1 + card {n. l \<le> n \<and> n < u - 1 \<and> m n = v}"
    by (simp add: t t3)
qed

lemma map_occ_left_no_add:
  fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>l < u\<close>
  assumes fact1: \<open>\<not>m l = v\<close>
  shows \<open>map_occ v m l u = map_occ v m (l + 1) u\<close>
  unfolding map_occ_def
  by (metis add1_zle_eq fact1 order.strict_iff_order)

lemma map_occ_left_add:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>l < u\<close>
  assumes fact1: \<open>m l = v\<close>
  shows \<open>map_occ v m l u = 1 + map_occ v m (l + 1) u\<close>
  unfolding map_occ_def
proof -
  have t1: "{n. l \<le> n \<and> n < u \<and> m n = v} = {l} \<union> {n. l + 1 \<le> n \<and> n < u \<and> m n = v}"
    unfolding set_eq_iff
    by (auto simp add: fact0 fact1)
  have t3: "finite {n. l + 1 \<le> n \<and> n < u \<and> m n = v}"
    using finite_Collect_conjI by force
  show "card {n. l \<le> n \<and> n < u \<and> m n = v} = 1 + card {n. l + 1 \<le> n \<and> n < u \<and> m n = v}"
    using t1 t3 by auto
qed

lemma map_occ_bounds:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes v :: \<open>'a\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  assumes fact0: \<open>l \<le> u\<close>
  shows \<open>0 \<le> map_occ v m l u\<close>
  and \<open>int (map_occ v m l u) \<le> u - l\<close>
  unfolding map_occ_def
proof blast
  have t1[simp]: "{n. l \<le> n \<and> n < u} = {l..<u}"
    by (auto simp add: set_eq_iff)
  have t2: "u - l = int (card {n. l \<le> n \<and> n < u})"
    by (auto simp add: fact0)
  show "int (card {n. l \<le> n \<and> n < u \<and> m n = v}) \<le> u - l"
    unfolding t2 Int.zle_int
    apply (rule card_mono)
    using finite_Collect_conjI by force+
qed


lemma map_occ_append:
        fixes l :: \<open>int\<close>
  fixes mid :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes v :: \<open>'a\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  assumes fact0: \<open>l \<le> mid\<close>
  assumes fact1: \<open>mid \<le> u\<close>
  shows \<open>map_occ v m l u = map_occ v m l mid + map_occ v m mid u\<close>
  unfolding map_occ_def
proof -
  have t1: "{n. l \<le> n \<and> n < u \<and> m n = v} = {n. l \<le> n \<and> n < mid \<and> m n = v} \<union> {n. mid \<le> n \<and> n < u \<and> m n = v}"
    apply (auto 10 10 simp add: set_eq_iff fact0 fact1)
    using fact1 fact0 by force+
  have t2: "finite {n. l \<le> n \<and> n < u \<and> m n = v}"
           "finite {n. l \<le> n \<and> n < mid \<and> m n = v}"
           "finite {n. mid \<le> n \<and> n < u \<and> m n = v}"
    using finite_Collect_conjI by force+
  have t3: "{n. l \<le> n \<and> n < mid \<and> m n = v} \<inter> {n. mid \<le> n \<and> n < u \<and> m n = v} = {}"
    by (auto 10 10 simp add: set_eq_iff fact0 fact1)
  show "card {n. l \<le> n \<and> n < u \<and> m n = v} = card {n. l \<le> n \<and> n < mid \<and> m n = v} + card {n. mid \<le> n \<and> n < u \<and> m n = v}"
    by (simp add: card_Un_disjoint t1 t2(2) t2(3) t3)
qed

lemma map_occ_neq:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>\<forall>(i :: int). l \<le> i \<and> i < u \<longrightarrow> \<not>m i = v\<close>
  shows \<open>map_occ v m l u = 0\<close>
  unfolding map_occ_def
  by (simp add: card_eq_0_iff fact0)


lemma map_occ_exists:
        fixes v :: \<open>'a\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  assumes fact0: \<open>0 < map_occ v m l u\<close>
  shows \<open>\<exists>(i :: int). (l \<le> i \<and> i < u) \<and> m i = v\<close>
  unfolding map_occ_def
  by (metis (mono_tags, lifting) fact0 map_occ_neq not_gr0)

lemma map_occ_pos:
        fixes l :: \<open>int\<close>
  fixes i :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  assumes fact0: \<open>l \<le> i\<close>
  assumes fact1: \<open>i < u\<close>
  shows \<open>0 < map_occ (m i) m l u\<close>
  unfolding map_occ_def
proof -
  have "finite {n. l \<le> n \<and> n < u \<and> m n = m i}"
    using finite_Collect_conjI by force+
  show "0 < card {n. l \<le> n \<and> n < u \<and> m n = m i}"
    using \<open>finite {n. l \<le> n \<and> n < u \<and> m n = m i}\<close> card_gt_0_iff fact0 fact1 by blast
qed

lemma map_occ_eq:
        fixes l :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes m1 :: \<open>int \<Rightarrow> 'a\<close>
  fixes m2 :: \<open>int \<Rightarrow> 'a\<close>
  fixes v :: \<open>'a\<close>
  assumes fact0: \<open>\<forall>(i :: int). l \<le> i \<and> i < u \<longrightarrow> m1 i = m2 i\<close>
  shows \<open>map_occ v m1 l u = map_occ v m2 l u\<close>
  unfolding map_occ_def
  by (metis fact0)


lemma map_occ_exchange:
        fixes l :: \<open>int\<close>
  fixes i :: \<open>int\<close>
  fixes u :: \<open>int\<close>
  fixes j :: \<open>int\<close>
  fixes z :: \<open>'a\<close>
  fixes m :: \<open>int \<Rightarrow> 'a\<close>
  fixes x :: \<open>'a\<close>
  fixes y :: \<open>'a\<close>
  assumes fact0: \<open>l \<le> i\<close>
  assumes fact1: \<open>i < u\<close>
  assumes fact2: \<open>l \<le> j\<close>
  assumes fact3: \<open>j < u\<close>
  assumes fact4: \<open>\<not>i = j\<close>
  shows \<open>map_occ z (m(j := y, i := x)) l u = map_occ z (m(j := x, i := y)) l u\<close>
  unfolding map_occ_def
  by (rule bij_betw_same_card[of "(\<lambda>k. if k = j then i else if k = i then j else k)"];
      auto simp add: bij_betw_def inj_on_def set_eq_iff image_iff fact0 fact1 fact2 fact3 fact4;
      insert fact4; blast)

  
section \<open> Euclidean Division \<close>

definition ediv :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "ediv" 70) where
  "a ediv b = sgn b * (a div \<bar>b\<bar>)"

definition emod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "emod" 70) where
  "a emod b = a mod \<bar>b\<bar>"

lemma ediv_div[simp]:
  \<open>b > 0 \<Longrightarrow> a ediv b = a div b\<close>
  \<open>b < 0 \<Longrightarrow> a ediv b = - (a div - b)\<close>
  unfolding ediv_def
  by force+

lemma emod_mod[simp]:
  \<open>b > 0 \<Longrightarrow> a emod b = a mod b\<close>
  \<open>b < 0 \<Longrightarrow> a emod b = a mod - b\<close>
  unfolding emod_def
  by force+

section \<open> Computer Division \<close>

definition cdiv :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "cdiv" 70) where
  "a cdiv b = sgn a * sgn b * (\<bar>a\<bar> div \<bar>b\<bar>)"

definition cmod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "cmod" 70) where
  "a cmod b = sgn a * (\<bar>a\<bar> mod \<bar>b\<bar>)"

lemma cdiv_div[simp]:
  \<open> a \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> a cdiv b = a div b \<close>
  \<open> a \<ge> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a cdiv b = - (a div - b) \<close>
  \<open> a \<le> 0 \<Longrightarrow> b > 0 \<Longrightarrow> a cdiv b = - (- a div b) \<close>
  \<open> a \<le> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a cdiv b = a div b \<close>
  unfolding cdiv_def
  by (cases \<open>a = 0\<close>; fastforce)+

lemma cmod_mod[simp]:
  \<open> a \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> a cmod b = a mod b \<close>
  \<open> a \<ge> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a cmod b = a mod - b \<close>
  \<open> a \<le> 0 \<Longrightarrow> b > 0 \<Longrightarrow> a cmod b = - (- a mod b) \<close>
  \<open> a \<le> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a cmod b = a mod b \<close>
  unfolding cmod_def
  by (cases \<open>a = 0\<close>; fastforce)+

lemma cDiv_mod:
  assumes \<open>y \<noteq> (0 :: int)\<close>
  shows \<open>x = y * (x cdiv y) + x cmod y\<close>
  unfolding cdiv_def cmod_def
  using assms
  by ((cases "y > 0"; cases "x > 0"; cases "x = 0"; auto),
      smt (verit, best) minus_mult_div_eq_mod,
      smt (verit, best) mult_div_mod_eq mult_minus_left)

declare [[quick_and_dirty]]

notation semiring_bit_operations_class.and (infixr \<open>AND\<close> 64)
     and semiring_bit_operations_class.or  (infixr \<open>OR\<close> 59)
     and semiring_bit_operations_class.xor (infixr \<open>XOR\<close> 59)

setup \<open>Context.theory_map (Default_Num_Typ.set (SOME \<^typ>\<open>int\<close>))\<close>

term uchar_of_char

end
