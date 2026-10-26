(* Dynamic arrays of static ABI elements consume a canonical prefix; trailing
   input bytes need not be part of that canonical encoding. *)
Theory abiValidStaticArray
Ancestors
  abiValidStaticAggregate abiValidStaticMembers abiValidStaticScalar abiCanonicalArrays
  vyperABI contractABI venomMemProofs byte words list rich_list arithmetic

Theorem abi_valid_static_array_values:
  !at cnt (raw_bytes:word8 list).
  ~is_dynamic at /\ valid_enc_array cnt (SOME (static_length at)) at raw_bytes raw_bytes ==>
  ?vs. dec_array cnt (SOME (static_length at)) at raw_bytes raw_bytes [] = ListV vs /\
    LENGTH vs = cnt /\
    enc (Tuple (REPLICATE cnt at)) (ListV vs) = TAKE (cnt * static_length at) raw_bytes /\
    cnt * static_length at <= LENGTH raw_bytes
Proof
  rpt gen_tac >> strip_tac >> drule abi_static_prefix_static >> strip_tac >>
  `EVERY (\ty. ~is_dynamic ty /\ abi_static_prefix ty) (REPLICATE cnt at)` by simp[] >>
  `valid_enc_tuple (REPLICATE cnt at) raw_bytes raw_bytes` by fs[valid_enc_tuple_REPLICATE] >>
  drule_all abi_valid_static_members >> disch_then (qspec_then `[]` strip_assume_tac) >>
  `~any_dynamic (REPLICATE cnt at)` by simp[any_dynamic_EXISTS] >>
  drule_all enc_tuple_static >> strip_tac >>
  qexists_tac `vs` >>
  gvs[abi_static_array_decode_tuple, LENGTH_REPLICATE, static_length_Tuple_SUM,
    map_replicate, SUM_REPLICATE, Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_valid_array_count_bytes:
  32 <= LENGTH bs ==>
  word_to_bytes (n2w (abi_head_word bs):256 word) T = TAKE 32 bs
Proof
  strip_tac >> simp[abi_head_word_def] >> irule word_bytes_roundtrip_proof >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[LENGTH_TAKE_EQ, dividesTheory.divides_def]
QED

Theorem abi_valid_static_array_prefix:
  ~is_dynamic at /\ valid_enc (Array NONE at) bs ==>
  LENGTH (enc (Array NONE at) (dec (Array NONE at) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (Array NONE at) (dec (Array NONE at) bs))) bs =
    enc (Array NONE at) (dec (Array NONE at) bs)
Proof
  strip_tac >>
  `32 <= LENGTH bs /\
   valid_enc_array (abi_head_word bs) (SOME (static_length at)) at (DROP 32 bs) (DROP 32 bs)` by
    (fs[Once valid_enc_def, abi_head_word_def, LET_THM] >>
     gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]) >>
  drule_all abi_valid_static_array_values >> strip_tac >>
  drule abi_valid_array_count_bytes >> strip_tac >>
  `dec (Array NONE at) bs = ListV vs` by
    asm_simp_tac bool_ss [Once dec_def, LET_THM, GSYM abi_head_word_def] >>
  `32 + abi_head_word bs * static_length at <= LENGTH bs` by (fs[LENGTH_DROP] >> decide_tac) >>
  `enc (Array NONE at) (dec (Array NONE at) bs) =
    TAKE (32 + abi_head_word bs * static_length at) bs` by
    asm_simp_tac bool_ss [canonical_array_tuple, enc_number_def, TAKE_SUM] >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_STATIC_ARRAY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid static array prefix not kernel closed: " ^ n)
  end) (DB.thms "abiValidStaticArray");
