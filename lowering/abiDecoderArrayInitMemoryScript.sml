(* Establish the finite-loop memory inputs from the executed initializer. *)
Theory abiDecoderArrayInitMemory
Ancestors
  abiDecoderArrayInitExec abiDecoderPrimitiveArrayFacts abiDecoderPrimitiveLoopContext
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract
  abiDecoderReservation abiDecoderContract abiDecoderFrame abiDecoderFrameCompose
  compileEnv valueEncoding vyperABI words list arithmetic

Theorem abi_decoder_array_init_frame_widen:
  abi_decode_footprint_frame [(d,32);(b,cap)] s t /\ 32 <= outsz ==>
  abi_decode_footprint_frame [(d,outsz);(b,cap)] s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d,32);(b,cap)]` >> simp[] >> rw[]
  >- (qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  qexistsl_tac [`b`, `cap`] >> simp[]
QED

Theorem abi_decoder_array_init_source:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  32 <= type_memory_bytes ce ty /\ abi_decode_footprint_frame [(d,32);(b,cap)] s t ==>
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc t) =
    enc (vyper_to_abi_type env ty) av
Proof
  strip_tac >> drule_all abi_decoder_array_init_frame_widen >> strip_tac >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  drule_all abi_decoder_source_frame >> simp[]
QED

Theorem abi_decoder_array_init_memory:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap s /\
  abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
  mem_word_at d t.vs_memory = n2w (LENGTH vs) /\ b <= slot /\ slot + 32 <= b + cap ==>
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 t /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot
    [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)]
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_array_init_source >> strip_tac >>
  `abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 t` by
    (irule abi_decoder_array_memory_init >> gvs[Once vyper_to_abi_type_def, Excl "enc_def"]) >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_decoder_pre_def, abi_decoder_ranges_def]) >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_reservation _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_reservation_def] >> strip_tac >> decide_tac) >>
  `slot + 32 <= d \/ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= slot` by
    (irule abi_decoder_arena_disjoint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `opc = MLOAD ==>
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot \/ slot + 32 <= sb`
    by (strip_tac >>
        `slot + 32 <= sb \/
         sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot` by
          (irule abi_decoder_arena_disjoint >> qexistsl_tac [`b`, `cap`] >>
           gvs[abi_footprint_disjoint_def, Once vyper_to_abi_type_def, Excl "enc_def"]) >>
        metis_tac[]) >>
  asm_simp_tac bool_ss [] >>
  gvs[abi_decoder_primitive_loop_data_def, abi_footprint_disjoint_def,
       Once vyper_to_abi_type_def, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_INIT_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array initialization memory not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayInitMemory");
