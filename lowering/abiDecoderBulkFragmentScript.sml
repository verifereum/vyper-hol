(* Typed execution and straight-line fragments for bulk dynamic-array decoding. *)
Theory abiDecoderBulkFragment
Ancestors
  abiDecoderBulkTyped abiDecoderBulk abiDecoderBulkContract
  abiDecoderTypedContract abiDecoderCoherence abiDecoderBytesTyped
  abiDecoderFrameCompose abiDecoderFrame abiDecoderContract
  abiEncoder exprLoweringProps compileEnv emitHelper valueEncoding
  fragExec venomExecSemantics venomState venomInst words rich_list

Theorem abi_decoder_typed_bulk_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
      st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s t
Proof
  strip_tac >> drule_all abi_decoder_bulk_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bulk_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory` by
    (qpat_assum `mem_sz = type_memory_size tv`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     mp_tac (Q.INST [`n` |-> `maxn`, `mem` |-> `t.vs_memory`,
       `source` |-> `abi_decode_source opc s`] static_dynarray_copied_layout) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> simp[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> irule abi_decode_frame_widen >>
  qexistsl_tac [`d`, `32 + LENGTH vs * mem_sz`] >> simp[]
QED

Theorem abi_decoder_bulk_shape:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  abi_decode_source_opcode opc /\ ~dec_info_needs_clamp ei ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_decoder_typed_bulk_fragment:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  frag_exec ctx st st'
    (abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
       (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
       (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap)
    (\t. ?s. abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
       (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
       (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s /\
       abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
         st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s t)
    (K F)
Proof
  reverse (Cases_on `abi_decode_source_opcode opc`)
  >- simp[frag_exec_def, abi_decoder_recursive_pre_def,
          abi_decoder_pre_def, abi_decoder_ranges_def] >>
  strip_tac >> drule_all abi_decoder_bulk_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_bulk_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx] >> qexists_tac `s` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_FRAGMENT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI typed bulk fragment not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkFragment");
