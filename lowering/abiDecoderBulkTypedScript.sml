(* Typed bulk dynamic-array decoding from canonical ABI source bytes. *)
Theory abiDecoderBulkTyped
Ancestors
  abiDecoderBulk abiDecoderBulkMetadata abiDecoderBulkContract
  abiDecoderCoherence abiDecoderLayout abiDecoderTypedContract
  abiStaticDynarrayLayout abiStaticLayoutProps abiCanonicalArrayLoad
  abiDecoderFrameCompose abiDecoderFrame valueEncoding vyperABI vyperTyping
  vyperValue contractABI compileEnv exprLowering words arithmetic byte

Theorem abi_bulk_typed_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_decoder_bulk_pre_facts:
  ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s ==>
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  abi_sz = mem_sz /\ mem_sz = type_memory_size tv /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  fresh_vars_wrt st s /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH vs) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  LENGTH vs * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + LENGTH vs * mem_sz <= d \/ d + 32 <= sb + 32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + LENGTH vs * abi_sz <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  32 + LENGTH vs * mem_sz <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  pure_rewrite_tac[abi_decoder_recursive_pre_def, abi_decoder_pre_def,
                   abi_decoder_metadata_def, abi_decoder_ranges_def] >> strip_tac >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  drule_all abi_decoder_typed_conversion >> strip_tac >>
  `vyper_to_abi_same env ty vs = SOME avs` by
    (qpat_x_assum `vyper_to_abi env (ArrayT _ _) _ = _` mp_tac >>
     simp[Once vyper_to_abi_def, AllCaseEqs()]) >>
  `all_have_type tv vs /\ LENGTH vs <= maxn` by fs[Once value_has_type_def] >>
  drule_all static_same_canonical_layout >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
   32 + LENGTH vs * type_memory_size tv` by
    simp[static_dynarray_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     (abi_decode_source opc s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[vyper_to_abi_type_def] >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH avs)` by
    (irule canonical_dynamic_array_count_load >>
     qexists_tac `vyper_to_abi_type env ty` >> fs[vyper_to_abi_type_def]) >>
  `LENGTH vs * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  gvs[vyper_to_abi_type_def, abi_footprint_disjoint_def, type_memory_bytes_def,
      DISJ_IMP_THM, FORALL_AND_THM, Excl "enc_def"] >>
  rpt strip_tac >> gvs[Excl "enc_def"] >> TRY decide_tac >>
  disj2_tac >> rename1 `eval_operand hi s = SOME (n2w hb)` >>
  qexists_tac `hb` >> simp[] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_TYPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI typed bulk decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkTyped");
