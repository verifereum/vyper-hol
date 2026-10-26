(* Select a typed child from the actual ABI conversion of a dynamic array. *)
Theory abiDecoderArrayChild
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiCanonicalArrayLoad abiDecodeRanges
  abiDecoderWordTyped abiDecoderLayout
  vyperABI vyperTyping vyperValue contractABI compileEnv valueEncoding words arithmetic list rich_list
Libs
  Omega

Theorem abi_decoder_word_child_intervals:
  !i count len src_base dst_base limit:num.
  i < count /\ 32 + i * 32 + 32 <= len /\
  dst_base + 32 + count * 32 < limit /\ src_base + len < limit ==>
  src_base + 32 + i * 32 < limit /\ dst_base + 32 + i * 32 < limit /\
  src_base + 32 + i * 32 + 32 <= src_base + len /\
  dst_base + 32 + i * 32 + 32 <= dst_base + 32 + count * 32
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_dynarray_metadata_child:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `evaluate_type env ty = SOME tv` by fs[abi_decoder_header_def] >>
  `abi_to_vyper_list env (REPLICATE (LENGTH (pre ++ av::post)) ty)
    (pre ++ av::post) = SOME (vpre ++ v::vpost)` by
    (qpat_x_assum `abi_to_vyper env (ArrayT _ _) _ = _` mp_tac >>
     simp[Once abi_to_vyper_def, make_array_value_def, AllCaseEqs()]) >>
  drule abi_to_vyper_list_EL >> strip_tac >>
  `abi_to_vyper env ty av = SOME v` by
    (qpat_x_assum `!i. i < LENGTH _ ==> _` (qspec_then `LENGTH pre` mp_tac) >>
     simp[EL_APPEND_EQN, EL_REPLICATE]) >>
  `value_has_type tv v` by fs[Once value_has_type_def, all_have_type_EVERY] >>
  `has_type (vyper_to_abi_type env ty) av` by
    (irule canonical_array_member_type >>
     qexistsl_tac [`NONE`, `post`, `pre`] >> fs[Once vyper_to_abi_type_def] >> gvs[]) >>
  drule_all abi_decoder_coherent_root_metadata >> simp[]
QED

Theorem abi_decoder_dynarray_primitive_metadata:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  type_memory_bytes ce ty = 32 /\ type_memory_size tv = 32 /\
  abi_member_head_size (vyper_to_abi_type env ty) = 32 /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = 32 /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ LENGTH pre < maxn
Proof
  strip_tac >> drule_all abi_decoder_dynarray_metadata_child >> strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `~is_dynamic (vyper_to_abi_type env ty) /\ type_memory_size tv = 32 /\
   abi_member_head_size (vyper_to_abi_type env ty) = 32`
    by fs[abi_decoder_header_def, abi_member_head_size_def] >>
  `value_has_type tv v /\ abi_to_vyper env ty av = SOME v`
    by fs[abi_decoder_metadata_def] >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (drule_all abi_decoder_descended_encoding_length >> asm_simp_tac bool_ss []) >>
  `LENGTH pre < maxn` by
    (qpat_assum `abi_decoder_metadata ce env (ArrayT _ _) _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_metadata_def] >> strip_tac >>
     fs[Once value_has_type_def] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_decoder_dynarray_primitive_source:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  mem_bytes_at (sb + 32 + LENGTH pre * 32) 32 (abi_decode_source opc s) =
    enc (vyper_to_abi_type env ty) av /\
  sb + 32 + LENGTH pre * 32 < dimword (:256) /\
  d + 32 + LENGTH pre * 32 < dimword (:256) /\
  sb + 32 + LENGTH pre * 32 + 32 <= sb +
    LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))) /\
  d + 32 + LENGTH pre * 32 + 32 <= d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  type_memory_size tv = 32
Proof
  strip_tac >> drule_all abi_decoder_dynarray_primitive_metadata >> strip_tac >>
  `has_type (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))` by
    fs[abi_decoder_metadata_def, Once vyper_to_abi_type_def] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_static_child_source)) >> strip_tac >>
  drule canonical_array_member_ranges >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32`
    by simp[Once type_memory_bytes_def] >>
  qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32` (fn parent_th =>
  qpat_assum `abi_member_head_size (vyper_to_abi_type env ty) = 32` (fn head_th =>
    qpat_assum `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` (fn len_th =>
      qpat_assum `LENGTH pre = LENGTH vpre` (fn prefix_th =>
        let val rewrites = [parent_th, head_th, len_th, prefix_th, ADD_ASSOC] in
          RULE_ASSUM_TAC (PURE_REWRITE_RULE rewrites) >> PURE_REWRITE_TAC rewrites
        end)))) >>
  asm_simp_tac bool_ss [ADD_ASSOC] >>
  irule abi_decoder_word_child_intervals >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array child metadata not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayChild");
