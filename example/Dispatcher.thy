theory Dispatcher

imports
  "../Parse"
  "../Hoare/HoareTripleForBasicBlocks"
  "./ToyExamplesBlocks"
  "../Word_Lib/Word_Lemmas_32"
begin

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def blocks_indexes_def build_basic_blocks_def
 aux_basic_block.simps add_address_def block_pt_def

abbreviation "blk_num \<equiv> block_number_pred"

lemma address_mask:
 "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 160"
  by (simp add: mask_def)

lemma address_mask_ucast:
 "ucast (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF && (ucast (w::address))::w256) = w"
  apply (simp add: ucast_ucast_mask address_mask ucast_mask_drop word_bool_alg.conj.commute)
  apply (simp add: mask_def)
  done

lemma ucast_and_w256_drop:
 "((ucast (w::address))::w256) && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = ucast w"
  by word_bitwise

definition
  bytestr_to_w256 :: "byte list \<Rightarrow> w256"  where
 "bytestr_to_w256 \<equiv> word_rcat"

lemma hash_diff:
  "ucast (hash::32 word) = (0xa9059cbb::w256) \<Longrightarrow> hash = 0xa9059cbb "
  "ucast (hash::32 word) = (0x70a08231::w256) \<Longrightarrow> hash = 0x70a08231 "
  "ucast (hash::32 word) = (0x18160ddd::w256) \<Longrightarrow> hash = 0x18160ddd "
  by word_bitwise+

lemma ucast_160_upto_256_eq:
  " ((ucast (x::160 word))::w256) = ucast y \<Longrightarrow> x = y"
  by (drule ucast_up_inj; simp)


lemma length_word_rsplit_32:
  "length (word_rsplit (x::w256)::byte list) = 32"
by(simp add: length_word_rsplit_exp_size' word_size)

lemma word_of_int_hash_not_0:
"word_of_int
 (bin_rcat 8
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) \<noteq>
(0::w256)"
by(simp add: bin_rcat_def bin_cat_def)

lemmas calldataload_simps=
read_word_from_bytes_def
byte_list_fill_right_def

lemmas words_simps=
word_of_int_hash_not_0
word_rcat_eq
length_word_rsplit_32

bundle dispatcher_bundle =
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  if_split[ split del ] sep_fun_simps[simp del]
  gas_value_simps[simp add] gas_simps[simp] pure_emp_simps[simp add]
  evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
  pure_false_simps[simp add] iszero_stack_def[simp add]
  word256FromNat_def[simp add]

lemma stack_height_not_stack:
  "stack n m s \<Longrightarrow> \<not> stack_height h s"
by(simp add: stack_height_def stack_def)

lemma memory_elm_not_stack:
"stack n m s \<Longrightarrow> \<not> memory8 h d s"
by(simp add: memory8_def stack_def)

lemma memory_range_not_stack:
"stack n m s \<Longrightarrow> \<not> memory_range h d s"
  including dispatcher_bundle
  apply(induction d arbitrary: h s; simp add: stack_def)
  apply(simp add: memory8_sep)
  done

lemma memory_not_stack:
"stack n m s \<Longrightarrow> \<not> memory h d s"
by(simp add: memory_def stack_def memory_range_not_stack)

lemma gas_pred_not_stack:
"stack n m s \<Longrightarrow> \<not> gas_pred h s"
by(simp add: gas_pred_def stack_def)

lemma continuing_not_stack:
"stack n m s \<Longrightarrow> \<not> continuing s"
by(simp add: continuing_def stack_def)

lemma sent_data_not_stack:
"stack n m s \<Longrightarrow> \<not> sent_data h s"
by(simp add: sent_data_def stack_def)

lemma sent_value_not_stack:
"stack n m s \<Longrightarrow> \<not> sent_value h s"
by(simp add: sent_value_def stack_def)

lemma memory_usage_not_stack:
"stack n m s \<Longrightarrow> \<not> memory_usage h s"
by(simp add: memory_usage_def stack_def)

lemma not_continuing_not_stack:
"stack n m s \<Longrightarrow> \<not> not_continuing s"
by(simp add: not_continuing_def stack_def)

lemma program_counter_not_stack:
"stack n m s \<Longrightarrow> \<not> program_counter p s"
by(simp add: program_counter_def stack_def)

lemma action_not_stack:
"stack n m s \<Longrightarrow> \<not> action a s"
by(simp add: action_def stack_def)

lemmas not_stack =
action_not_stack
program_counter_not_stack
not_continuing_not_stack
memory_usage_not_stack
sent_value_not_stack
sent_data_not_stack
continuing_not_stack
gas_pred_not_stack
memory_not_stack
memory_range_not_stack
stack_height_not_stack
memory_elm_not_stack

lemma stack_height_first:
"(a \<and>* stack_height h \<and>* b) = (stack_height h \<and>* a \<and>* b)"
by(rule sep.mult.left_commute)

lemma gas_pred_first:
"(a \<and>* gas_pred g \<and>* b) = (gas_pred g \<and>* a \<and>* b)"
by(rule sep.mult.left_commute)

lemma stack_first:
"\<forall>n m s. stack n m s \<longrightarrow> \<not> a s \<Longrightarrow>
(a \<and>* stack h d \<and>* b) = (stack h d \<and>* a \<and>* b)"
by(rule sep.mult.left_commute)

method order_sep_conj=
(simp add: gas_pred_first)?,
(simp add: stack_first not_stack)?,
(simp add: stack_height_first)?

method blocks_rule_vcg=
rule blocks_jumpi_uint |
rule blocks_jump_uint |
rule blocks_next |
rule blocks_no

method sep_imp_solve uses simp =
   solves \<open>rule conjI; rule refl\<close>
 | solves \<open>match conclusion in "block_lookup _ _ = Some _"  \<Rightarrow> \<open>simp add:word_rcat_simps\<close>
             , (rule conjI, (rule refl)+)\<close>
 | solves \<open>simp\<close>
 | solves \<open>(clarsimp?, order_sep_conj, ((((sep_cancel, clarsimp?)+)|simp add:simp|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp?, order_sep_conj, ((((sep_cancel, clarsimp?)+)|(clarsimp split:if_split simp: simp)|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp split:if_splits simp:word_rcat_simps) ; sep_imp_solve \<close>

method split_conds =
 (split if_split_asm; clarsimp simp add: word_rcat_simps)?

method block_vcg uses simp=
  split_conds,
  ((blocks_rule_vcg; (rule refl)?), triple_seq_vcg),
  (sep_imp_solve simp:simp)+,
  (solves \<open>split_conds\<close>)?

method triple_blocks_vcg =
  (clarsimp simp only: sep_conj_ac(2)[symmetric])?,
  ((rule blocks_jumpi_uint_ex blocks_jump_uint_ex blocks_no_ex blocks_next_ex); 
   (clarsimp simp only: sep_conj_ac(2))?),
  triple_seq_vcg

definition w256 :: "'a::len0 word \<Rightarrow> w256"  where
 "w256 v \<equiv> ucast v"

definition bytestr :: "'a::len0 word \<Rightarrow> byte list"  where
 "bytestr \<equiv> word_rsplit"

type_synonym erc20_balances = "address \<rightharpoonup> w256"

definition balance_upd :: "address \<Rightarrow> (w256 \<Rightarrow> w256) \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
  where
 "balance_upd addr upd m \<equiv> m(addr \<mapsto> upd (the (m addr)))"

definition
 transfer :: "address \<Rightarrow> address \<Rightarrow> w256 \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
 where
 "transfer from to amount m \<equiv> balance_upd to (\<lambda>v. v + amount) (balance_upd from (\<lambda>v. v - amount) m)"

definition
 zero :: "address \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
 where
 "zero addr m \<equiv> m(addr \<mapsto> 0)"

definition
 balances_mapping :: "address \<Rightarrow> w256"
 where
 "balances_mapping addr \<equiv>  keccak (bytestr (w256 addr) @ bytestr (0::w256))"

definition
 balances_to_storage :: "erc20_balances \<Rightarrow> state_element set \<Rightarrow> bool"
 where
 "balances_to_storage m s \<equiv> s = (\<lambda>addr. StorageElm (balances_mapping addr, the (m addr))) ` dom m"

definition
 addrs_hash_consistency :: "address set \<Rightarrow> bool"
 where
 "addrs_hash_consistency s \<equiv>
   \<forall>a1\<in>s.\<forall>a2 \<in> s. a1 \<noteq> a2 \<longrightarrow> balances_mapping a1 \<noteq> balances_mapping a2"

lemma balances_to_storage_sep':
 "addrs_hash_consistency (dom m)
 \<Longrightarrow> m addr = Some v
 \<Longrightarrow>  balances_to_storage m = (storage (balances_mapping addr) v ** balances_to_storage (m(addr:=None)))"
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp simp add: sep_basic_simps balances_to_storage_def storage_def)
   apply (fastforce simp: balances_mapping_def addrs_hash_consistency_def image_def)
  apply (clarsimp simp: balances_to_storage_def sep_basic_simps  split:if_splits)
  apply (simp add: image_def storage_def)
  apply (rule equalityI)
   apply fastforce
  apply fastforce
  done

lemma balances_to_storage_sep:
 "addrs_hash_consistency (insert addr (dom m))
 \<Longrightarrow> balances_to_storage (m(addr\<mapsto>v)) = (storage (balances_mapping addr) v ** balances_to_storage (m(addr:=None)))"
  by (subst  balances_to_storage_sep'[where addr=addr and v=v]; simp)

lemma balances_to_storage_singleton:
 "a1 \<noteq> a2
 \<Longrightarrow> balances_to_storage ([a1 \<mapsto> v](a2 := None)) = (storage (balances_mapping a1) v)"
  apply (rule ext)
  apply ( simp add: balances_to_storage_def storage_def image_def)
  done

lemma transfer_sep:
 "addrs_hash_consistency {a2,a1}
  \<Longrightarrow> a1 \<noteq> a2
  \<Longrightarrow> (balances_to_storage (transfer a1 a2 v1 ([a1\<mapsto>v1, a2\<mapsto>v2])) ** R) = (storage (balances_mapping a2) (v2 + v1) \<and>* storage (balances_mapping a1) 0 \<and>* R)"
  apply (simp add: transfer_def balance_upd_def)
  apply (sep_simp simp: balances_to_storage_sep)
  apply simp
  apply (sep_simp simp: balances_to_storage_sep)
  apply (simp add: sep_conj_assoc sep_conj_commute)
  apply (sep_simp simp: balances_to_storage_singleton)
  apply (simp)+
  done

lemma length_word_rsplit_4:
"length (word_rsplit (x::32 word)::byte list) = 4"
by(simp add: length_word_rsplit_exp_size' word_size)


lemma power_mult:
"((\<lambda>s. s * (x::int)) ^^ m) = (\<lambda>s. s * (x ^ m))"
apply(rule ext)
apply(induction m; simp)
done

lemma div_mult2_eq_word:
"unat b * unat d < 2 ^ len_of TYPE('a) \<Longrightarrow>
(a:: 'a :: len word) div (b * d) = a div b div d"
  apply unat_arith
  apply clarsimp
  apply (subst unat_mult_lem [THEN iffD1], simp)
  apply(rule div_mult2_eq)
done

lemma word_mult_left_cancel: 
  "(0 :: 'a :: len word) < y \<Longrightarrow> unat x * unat y < 2 ^ len_of TYPE('a) \<Longrightarrow>
   unat z * unat y < 2 ^ len_of TYPE('a) \<Longrightarrow>
    (x * y = z * y) = (x = z)"
  apply unat_arith
  apply clarsimp
  apply(rule iffI)
   defer
   apply(simp)
  apply(drule unat_cong)
  apply (subst (asm)unat_mult_lem [THEN iffD1], simp)
  apply(simp)
  apply (subst (asm)unat_mult_lem [THEN iffD1], simp)
  apply auto
  done

lemma word_rcat_div_1_a_not0:
"a \<noteq> 0 \<Longrightarrow>
 n \<le> 27 \<Longrightarrow>
 m \<le> 27 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate (Suc n) 0))::w256) div
(word_rcat ([1::byte] @ (replicate (Suc m) 0))::w256) =
(word_rcat ([a,b,d,e] @ (replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate m 0))::w256)"
apply(simp add: word_rcat_def bin_rcat_def bin_cat_num)
apply(rule subst[OF mult.commute])
apply(simp add: foldl_conv_fold power_mult)
apply(subst Word.word_ubin.norm_Rep[where x=a, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=b, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=d, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=e, simplified])+
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. x div _ = _"])
apply(rule subst[OF wi_hom_mult[where b=256 and a="16777216 * uint a + 65536 * uint b + 256 * uint d + uint e", simplified], where P="\<lambda>x. x * _ div _ = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ div x = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ = x div _"])
apply(simp add: mult.commute)
apply(subst div_mult2_eq_word)
 apply(simp add: unat_def uint_word_of_int)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst int_mod_eq')
   apply(simp)
  apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=32 and a=256, simplified])
  apply(simp)
 apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=31 and a=256, simplified])
 apply(simp)
apply(simp add: mult.assoc mult.commute[where a="0x100"])
apply(simp add: sym[OF mult.assoc])
apply(subst Word.word_div_mult)
  apply(simp_all)
apply(subgoal_tac "f > 0")
 apply(simp add: unat_def)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst wi_hom_mult)
 apply(subst sym[OF word_less_alt[where a="word_of_int (f * 256^n)" and b="word_of_int (uint (2^248::w256))::w256", simplified]])
 apply(subst wi_less[where n="f * 256^n" and m="uint (2^248::w256)" and 'a=256, simplified])
   apply(subgoal_tac "f < 256 ^4"; simp)
	apply(subst int_mod_eq'[where l="2^256", simplified]; simp?)
   apply(rule mult_strict_mono[where d="256^28::int" and b=4294967296, simplified]; simp?)
   apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=28 and a=256, simplified], simp)
  apply(rule mult_less_le_imp_less[where d="256^27::int" and b=4294967296, simplified]; simp?)
  apply(rule Power.linordered_semidom_class.power_increasing[where N=27 and a=256, simplified], simp)
 apply(drule sym; simp)
 apply(insert uint_lt[where w="a"])[1]
 apply(insert uint_lt[where w="b"])[1]
 apply(insert uint_lt[where w="d"])[1]
 apply(insert uint_lt[where w="e"])[1]
 apply(simp)
apply(drule sym; simp)
apply(subgoal_tac "uint a > 0")
 apply(insert uint_0[where w=b])[1]
 apply(insert uint_0[where w=d])[1]
 apply(insert uint_0[where w=e])[1]
 apply(arith)
apply(insert uint_0[where w=a])[1]
apply(subgoal_tac "uint a \<noteq> 0")
 apply(arith)
apply(rule notI)
apply(simp add: uint_0_iff)
done

method word32_not_0_aux=
		 (subgoal_tac "uint a > 0"),
	  (arith),
	 (subgoal_tac "uint a \<noteq> 0"),
	  (arith),
	 (rule notI),
	 (simp add: uint_0_iff)

lemma word32_not_0:
	"\<And>a b d e.(a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0) \<Longrightarrow> (uint a * 16777216 + uint b * 65536 + uint d * 256 + uint e) > 0"
apply(cut_tac w=a in uint_0)
apply(cut_tac w=b in uint_0)
apply(cut_tac w=d in uint_0)
apply(cut_tac w=e in uint_0)
	apply(erule disjE, word32_not_0_aux)
	apply(erule disjE)
		apply(rename_tac b a d e, word32_not_0_aux)
	apply(erule disjE)
		apply(rename_tac d b a e, word32_not_0_aux)
	apply(rename_tac e b d a, word32_not_0_aux)
done
	
lemma word_rcat_div_1:
"a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0 \<Longrightarrow>
 n \<le> 27 \<Longrightarrow>
 m \<le> 27 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate (Suc n) 0))::w256) div
(word_rcat ([1::byte] @ (replicate (Suc m) 0))::w256) =
(word_rcat ([a,b,d,e] @ (replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate m 0))::w256)"
apply(simp add: word_rcat_def bin_rcat_def bin_cat_num)
apply(rule subst[OF mult.commute])
apply(simp add: foldl_conv_fold power_mult)
apply(subst Word.word_ubin.norm_Rep[where x=a, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=b, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=d, simplified])+
apply(subst Word.word_ubin.norm_Rep[where x=e, simplified])+
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. x div _ = _"])
apply(rule subst[OF wi_hom_mult[where b=256 and a="16777216 * uint a + 65536 * uint b + 256 * uint d + uint e", simplified], where P="\<lambda>x. x * _ div _ = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ div x = _"])
apply(rule subst[OF wi_hom_mult, where P="\<lambda>x. _ = x div _"])
apply(simp add: mult.commute)
apply(subst div_mult2_eq_word)
 apply(simp add: unat_def uint_word_of_int)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst int_mod_eq')
   apply(simp)
  apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=32 and a=256, simplified])
  apply(simp)
 apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=31 and a=256, simplified])
 apply(simp)
apply(simp add: mult.assoc mult.commute[where a="0x100"])
apply(simp add: sym[OF mult.assoc])
apply(subst Word.word_div_mult)
  apply(simp_all)
apply(subgoal_tac "f > 0")
 apply(simp add: unat_def)
 apply(subst nat_mono_iff[where z="2^248", simplified])
 apply(subst wi_hom_mult)
 apply(subst sym[OF word_less_alt[where a="word_of_int (f * 256^n)" and b="word_of_int (uint (2^248::w256))::w256", simplified]])
 apply(subst wi_less[where n="f * 256^n" and m="uint (2^248::w256)" and 'a=256, simplified])
   apply(subgoal_tac "f < 256 ^4"; simp)
	apply(subst mod_pos_pos_trivial[where l="2^256", simplified]; simp?)
   apply(rule mult_strict_mono[where d="256^28::int" and b=4294967296, simplified]; simp?)
   apply(rule Power.linordered_semidom_class.power_strict_increasing[where N=28 and a=256, simplified], simp)
  apply(rule mult_less_le_imp_less[where d="256^27::int" and b=4294967296, simplified]; simp?)
  apply(rule Power.linordered_semidom_class.power_increasing[where N=27 and a=256, simplified], simp)
 apply(drule sym; simp)
 apply(insert uint_lt[where w="a"])[1]
 apply(insert uint_lt[where w="b"])[1]
 apply(insert uint_lt[where w="d"])[1]
 apply(insert uint_lt[where w="e"])[1]
 apply(simp)
apply(drule sym; simp add: mult.commute)
apply(rule word32_not_0[simplified], assumption)
done

lemma word_rcat_div1:
"a \<noteq> 0 \<or> b\<noteq>0 \<or> d\<noteq>0 \<or> e\<noteq>0 \<Longrightarrow>
 n \<le> 28 \<Longrightarrow>
16777216 * uint a + 65536 * uint b + 256 * uint d + uint e = f \<Longrightarrow>
((word_rcat ([a::byte,b,d,e] @ replicate n 0))::w256) div
(word_rcat ([1::byte] @ (replicate n 0))::w256) =
(word_rcat ([a,b,d,e])::w256)"
apply(induction n; simp)
 apply(subgoal_tac "word_rcat [1::byte] = (1::(w256))")
  apply(simp add: word_div_def)
 apply(simp add: word_rcat_simps)
apply(subst word_rcat_div_1[simplified]; simp)
done

definition bit_mask :: "32 word \<Rightarrow> 256 word" where
"bit_mask z =  4294967295 AND
    word_of_int
     (uint
       (word_rcat
         (word_rsplit z @
          [0::byte, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 0, 0])::w256) div
      26959946667150639794667015087019630673637144422540572481103610249216)"

lemma w:
 "  word_rsplit w = sw \<Longrightarrow>
  \<forall>k m. k < length sw \<longrightarrow> m < size (hd sw) \<longrightarrow>
  rev sw ! k !! m = w !! (k * size (hd sw) + m)"
apply (clarsimp)
apply (rule test_bit_rsplit[OF sym, rule_format] ; simp)
done

lemma list0_x:
"\<forall>k<Suc (Suc (Suc (Suc 0))).
       \<forall>m<8.
          [0, 0, 0, 0::byte] ! k !! m = z !! (k * 8 + m) \<Longrightarrow>
n <32 \<Longrightarrow>
    \<not> z !! n"
apply(drule_tac x="n div 8" in spec)
apply(drule mp)
apply unat_arith
apply(drule_tac x="n mod 8" in spec)
 apply(drule mp, arith)
apply(simp)
apply(subgoal_tac "[0, 0, 0, 0] ! (n div 8) = (0::byte)")
apply(simp)
apply(subgoal_tac "n div 8 < 4")
apply (subst nth_Cons', clarsimp  split: if_split)+
apply (unat_arith)
done

lemma word_rsplit_0':
	"word_rsplit (z::32 word) = [0,0,0,0::byte] \<Longrightarrow>
	z =0"
apply (drule w)
apply clarsimp
apply (simp add: word_size)
apply (word_bitwise)
apply ((rule conjI)?, erule list0_x, simp)+
done

lemma word_rcat_nul_bits:
"n \<ge> 32 \<Longrightarrow>  \<not>((word_rcat ([a,b,d,e]::byte list))::w256) !! n"
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
apply(simp add: bintrunc_def)
done

lemma word_rsplit_32:
"\<exists>a b d e. word_rsplit (z::32 word) = [a,b,d,e::byte]"
apply(insert length_word_rsplit_4[where x=z])
apply(case_tac "word_rsplit z::byte list")
 apply(simp)
apply(rename_tac list, case_tac list, simp)
apply(rename_tac list, case_tac list, simp)
apply(rename_tac list, case_tac list, simp)
  apply(simp)
done

lemma word_rcat_rsplit_ucast:
"(word_rcat (word_rsplit z::byte list)::w256) = ucast (z::32 word)"
 apply(simp add: ucast_def)
 apply (rule word_eqI)
 apply(case_tac "n < 32")
  apply (clarsimp simp add : test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size 
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
  apply safe
     apply(subst (asm) word_test_bit_def, assumption)
    apply(arith)
   apply(subst word_test_bit_def, assumption)
  apply(drule leI)
  apply(insert word_rsplit_32[where z=z], clarsimp)[1]
  apply(drule_tac a=a and b=b and d=d and e=e in word_rcat_nul_bits, simp)
 apply(drule leI)
 apply(drule bin_nth_uint_imp, simp)
done

lemma word_rcat_bits_eq:
"n < 32 \<Longrightarrow>  ((word_rcat (word_rsplit z::byte list))::w256) !! n = (z::32 word) !! n"
apply(insert word_rsplit_32[where z=z])
apply(clarsimp)
apply(simp add: word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
apply(simp add: bintrunc_def)
oops

lemma word_rcat_rsplit_max: "(word_rcat [a,b,d,e::byte]::w256) \<le> mask 32"
apply(subst le_mask_iff)
  apply (rule word_eqI)
 apply (subst nth_shiftr)
  apply(simp add: word_size)
  apply(simp add: word_rcat_nul_bits)
done

lemma
	eval_bit_mask':
	"bit_mask z = word_rcat (word_rsplit (z::32 word)::byte list)"
	apply(simp add: bit_mask_def)
  apply(subgoal_tac "\<exists>a b d e. word_rsplit (z::32 word) = [a::byte,b,d,e]")
	apply(rule subst[OF uint_div[where x="word_rcat
         (word_rsplit z @
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           0])" and y="26959946667150639794667015087019630673637144422540572481103610249216::w256", simplified],
          where P="\<lambda>x. _ AND word_of_int x = _"])
  apply(case_tac "z\<noteq>0")
  apply(clarsimp)
   apply(cut_tac a=a and b=b and d=d and e=e and n=28 in word_rcat_div1)
   apply(subgoal_tac "\<not>([a::byte,b,d,e] = [0,0,0,0::byte])")
    apply(simp)
   apply(rule notI)
    apply(drule sym[where s="word_rsplit _"]; simp)
    apply(drule word_rsplit_0')
   apply(simp)+
   apply(subgoal_tac "word_rcat [1::byte, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
        (0x100000000000000000000000000000000000000000000000000000000::w256)")
    apply(clarsimp)
   (* apply(thin_tac _, thin_tac _,thin_tac _, thin_tac _) *)
   apply(thin_tac "word_rcat _ = _", thin_tac " _ = word_rcat _")
   apply (subgoal_tac "0xFFFFFFFF = (mask 32::256 word)")
   apply(simp only:word_bw_comms)
 apply (subst word_bw_comms(1))
   apply (subst le_mask_imp_and_mask)
   apply(rule word_rcat_rsplit_max)
apply(simp)
apply(simp add: mask_def)
apply(thin_tac _)+
apply(simp add: word_rcat_simps bin_cat_def)
apply(clarsimp)
apply(subst (asm) Word_Lemmas_32.word_rsplit_0)
apply(clarsimp simp add: word_rcat_simps bin_cat_def)
apply(rule word_rsplit_32)
done

lemma
	eval_bit_mask:
	"bit_mask z = ucast (z::32 word)"
apply(subst eval_bit_mask')
apply(subst word_rcat_rsplit_ucast)
apply(rule refl)
done


lemma bit_mask_noteq:
"x \<noteq> y \<Longrightarrow> bit_mask x \<noteq> bit_mask y"
apply(rule notI)
apply(subst (asm) eval_bit_mask)+
apply(drule up_ucast_inj; simp)
done

method bit_mask_solve=
(insert length_word_rsplit_4[where x=z])[1],
(split if_split_asm; simp)+,
(drule bit_mask_noteq),
(subst (asm) eval_bit_mask)+,
(simp add: ucast_def)

lemmas bit_mask_rev = sym[OF bit_mask_def]
lemma len_bytestr_simps: 
 "\<And>x. length (bytestr (x::32 word)) = 4"
 "\<And>x. length (bytestr (x::64 word)) = 8"
 "\<And>x. length (bytestr (x::256 word)) = 32"
  by(simp add: bytestr_def length_word_rsplit_exp_size' word_size)+

lemma two_power_of_224:
 "(0x100000000000000000000000000000000000000000000000000000000::nat) = 2^224"
  by simp


(* *** word_rcat shifts more generally *** *)
lemma concat_map_take :
"\<forall>x \<in> set xs. length (f x) = n \<Longrightarrow>
List.concat (map f (take k xs)) = take (k*n) (List.concat (map f xs))"
  apply(induct xs arbitrary: k, simp)
  apply(case_tac k, simp)
  apply clarsimp
  done


lemma word_rcat_shiftr_take : 
"length ys = 32 \<Longrightarrow> k \<le> 32 \<Longrightarrow>
 word_rcat (ys::byte list) >> 8 * k = (word_rcat (take (length ys - k) ys) ::w256)"
  apply (simp add: word_rcat_bl shiftr_bl)
  apply (simp add: word_rep_drop size_rcat_lem)
  apply(subst concat_map_take[where n=8])
   apply clarsimp
  apply(subst diff_mult_distrib)
  apply simp
  apply(subst Groups.ab_semigroup_mult_class.mult.commute)
  by(rule refl)

lemma word_rcat_append_shiftr :
  "length ys + length xs = 32 \<Longrightarrow>
   word_rcat ((ys::byte list) @ xs) >> (8 * length xs) = (word_rcat ys :: w256)"
  by(subst word_rcat_shiftr_take, simp_all)
(* ************************************************ *)  

lemma take_32_of_w256:
  fixes w1::byte and w2 :: byte and w3 :: byte and w4 :: byte and xs :: "bool list"
  shows
 "length xs = 224 \<Longrightarrow> 
  take 32 (to_bl (of_bl (to_bl w1 @ to_bl w2 @ to_bl w3 @ to_bl w4 @ xs) :: 256 word)) =
   take 32 (to_bl w1 @ to_bl w2 @ to_bl w3 @ to_bl w4)"
  by (simp add: word_rep_drop)

lemma word_rcat_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat ([a::byte, b, d, e] @ xs)::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat [a, b, d, e]"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply(subgoal_tac "unat (word_rcat (a # b # d # e # xs) >> 224) = 
                     unat (word_rcat ([a, b, d, e] @ xs) >> 8 * length xs)")
   apply(erule ssubst, subst word_rcat_append_shiftr)
    apply simp
   apply(rule refl)
  by simp

lemma word_rcat_word_rsplit_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat (word_rsplit (w::32 word) @ (xs::byte list))::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat (word_rsplit w :: byte list)"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply(subgoal_tac "unat (word_rcat (word_rsplit w @ xs) >> 224) = 
                     unat (word_rcat (word_rsplit w @ xs) >> 8 * length xs)")
   apply(erule ssubst, subst word_rcat_append_shiftr)
    apply(simp add: length_word_rsplit_4)
   apply(rule refl)
  by simp

(* ? ? ? ?
lemma take_to_bl_of_bl_word_list:
  fixes w::"'b::len0 word"
    and w'::"'a::len0 word"
    and xs :: "bool list"
  shows
 "length xs = LENGTH('b) - LENGTH('a) \<Longrightarrow>
  w = of_bl (to_bl w' @ xs) \<Longrightarrow>
  LENGTH('b) > LENGTH('a) \<Longrightarrow>
  take LENGTH('a) (to_bl w) =
   take LENGTH('a) (to_bl w')"
  by (simp add: word_rep_drop)

lemma take_32_concat_to_bl_word_rsplit:
  fixes w :: "32 word"
  and xs :: "byte list"
  shows
  "length xs = 28 \<Longrightarrow>
    take 32 (to_bl (of_bl (List.concat (map to_bl (word_rsplit w :: byte list)) @ List.concat (map to_bl xs)):: w256)) =
    List.concat (map to_bl (word_rsplit w :: byte list))"
  by (simp add:word_rev_tf takefill_alt size_rcat_lem length_word_rsplit_4)

lemma word_rcat_word_rsplit_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat (word_rsplit (w::32 word) @ (xs::byte list))::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat (word_rsplit w :: byte list)"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply (simp add: word_rcat_bl shiftr_bl)
  apply (rule arg_cong[where f=of_bl])
  apply (simp add: take_32_concat_to_bl_word_rsplit)
  done
*)


lemma w256_mask_32:
  "(0xFFFFFFFF::w256) = mask 32"
  by (simp add: mask_def)

lemma unat_ucast:
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "unat (UCAST ('a::len0\<rightarrow>'b::len) x) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
  apply (rule assms)
   apply simp
  done

lemma ucast_le_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> (UCAST('a::len0\<rightarrow>'b::len) x \<le> (ucast y)) = (x \<le> y)"
  by (simp add: word_le_nat_alt unat_ucast)

lemma minus_1_w32:
  " (-1::32 word) = 0xffffffff"
  by simp

lemma ucast_32_256_minus_1_eq:
  "UCAST(32 \<rightarrow> 256) (- 1) = 0xFFFFFFFF"
  apply (simp add: ucast_def unat_arith_simps unat_def)
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (clarsimp split: uint_splits)
  apply (simp add: minus_1_w32)
  done

lemma ucast_frm_32_le_mask_32:
 "UCAST(32\<rightarrow>256) z \<le> mask 32"
  apply (subgoal_tac "mask 32 = UCAST(32\<rightarrow>256) (mask 32)")
   apply (simp add: ucast_le_ucast mask_32_max_word)
  apply (simp add: mask_def)
  apply (simp add: ucast_32_256_minus_1_eq)
  done

lemma dispatcher_hash_extract:
 "length xs = 28 \<Longrightarrow>
  0xFFFFFFFF && word_of_int (uint (word_rcat (bytestr (z::32 word) @ xs) :: w256) div
      0x100000000000000000000000000000000000000000000000000000000) =
    (word_rcat (bytestr z)::w256)"
  apply (simp add: bytestr_def)
  apply(rule subst[where P="\<lambda>x. _ AND word_of_int x = _"])
  apply (rule uint_div[where x="word_rcat (word_rsplit z @ xs)"
        and y="0x100000000000000000000000000000000000000000000000000000000::w256", simplified])
  apply (subst word_rcat_word_rsplit_div_rep0; simp)
  apply (simp add: w256_mask_32)
  apply (subst word_bw_comms(1))
  apply (simp add: and_mask_eq_iff_le_mask)
  apply (simp add: word_rcat_rsplit_ucast)
  apply (simp add: ucast_frm_32_le_mask_32)
  done

lemma word_rsplit_byte_split:
"(word_rsplit (w1::w256) :: byte list) =
       a # aa # ab # ac # ad # ae # af # ag # ah # ai # aj #
 ak # al # am # an # ao # ap # aq # ar # as # a't # au # av #
 aw # ax # ay # az # ba # bb # bc # bd # be # lisue  \<Longrightarrow> lisue = []"
  using length_word_rsplit_32[where x=w1]
  by simp

lemma memory_range_0_w256_append:
  "(memory_range 0 (word_rsplit (w1::w256)) \<and>* memory_range 0x20  (word_rsplit (w2::w256))) =
     memory_range 0 (word_rsplit w1 @ word_rsplit w2)"
  including dispatcher_bundle
  apply (rule ext)
  apply (case_tac "(word_rsplit w1 :: byte list)")
   apply (simp add: length_0_conv[symmetric])
  apply (rename_tac list , case_tac list, solves \<open>simp add: list_eq_iff_zip_eq[where xs="word_rsplit _"]\<close>)+
  apply (simp add:)
  apply (drule word_rsplit_byte_split)
  apply simp
  done

lemma two_memory_memory_range_eq:
 "(R' \<and>* memory 0x20 w2 \<and>* R  \<and>* memory 0 w1  \<and>* R'') = (memory_range 0 (word_rsplit w1 @ word_rsplit w2) \<and>* R' \<and>* R  \<and>* R'')"
  by (simp add: memory_def, simp add: ac_simps, sep_simp simp: memory_range_0_w256_append)

lemma  stack_topmost_unfold_sep:
  "(stack_topmost h [a, b, c, d, e] ** R)
  = (stack_height (Suc (Suc (Suc (Suc (Suc h))))) ** stack h a ** stack (Suc h) b  ** stack (Suc (Suc h)) c** stack (Suc (Suc (Suc h))) d  
  ** stack (Suc (Suc (Suc (Suc h)))) e ** R)"
  apply (unfold stack_topmost_def)
  apply clarsimp
  apply (rule ext)
  apply (rule iffI)
  apply (clarsimp simp add: sep_basic_simps stack_def stack_height_def )
  apply (rule_tac x="insert (StackElm (Suc (Suc (Suc (Suc h))), e))
                 (insert (StackElm (Suc (Suc (Suc h)), d))
                   (insert (StackElm (Suc (Suc h), c))
                     (insert (StackElm (Suc h, b)) (insert (StackElm (h, a)) y))))" in exI)
  apply clarsimp
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d),
                      StackElm (Suc (Suc h), c), StackElm (Suc h, b)} \<union> y" in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d),
                      StackElm (Suc (Suc h), c)} \<union> y" in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d) } \<union> y" in exI)
   apply clarsimp
  
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e) } \<union> y" in exI)
 
   apply clarsimp
   apply blast  
  apply (clarsimp simp add: sep_basic_simps stack_def stack_height_def )
  apply (drule_tac x=ye in spec)
  apply blast
  done

lemma sep_stack_topmost_unfold_sep:
  "(R' ** stack_topmost h [a, b, c, d, e] ** R)
  = (R' ** stack_height (Suc (Suc (Suc (Suc (Suc h))))) ** stack h a ** stack (Suc h) b  ** stack (Suc (Suc h)) c** stack (Suc (Suc (Suc h))) d  
  ** stack (Suc (Suc (Suc (Suc h)))) e ** R)"
  by (sep_simp simp: stack_topmost_unfold_sep)

lemma memory_range_last:
 "unat (len::w256) = length data \<Longrightarrow> 
  (a \<and>* memory_range st data \<and>* b) = (a \<and>* b \<and>*  memory_range st data)"
 by (sep_simp simp: memory_range_sep)+

end
