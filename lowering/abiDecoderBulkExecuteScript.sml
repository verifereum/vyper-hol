(* Execute the actual bulk decoder from a fixed initial state, preserving budget. *)
Theory abiDecoderBulkExecute
Ancestors
  abiDecoderBulkFragment abiDecoderBulk abiDecoderBulkBody abiDecoderBulkPayload
  abiDecoderBytesTyped abiDecoderComposition abiDecoderBulkTyped abiDecoderVarSequence
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuardLE abiDecoderGuards abiDecoderCopy abiDecoderTypedContract
  abiDecoderCoherence abiDecoderArrayPrepare abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderContract abiDecoderLoop abiDecoderFrame abiDecoderFrameCompose
  fragExec instIdxIndep exprLoweringProps emitHelperProps emitHelper compileEnv
  venomExecSemantics venomState venomInst valueEncoding words list rich_list arithmetic

Theorem abi_decoder_bulk_allocation_shape:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ abi_decode_source_opcode opc /\ ~dec_info_needs_clamp ei ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_bulk_phases, abi_decode_source_opcode_def,
    abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
    abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
    abi_decode_le_guard_def, abi_decode_bulk_body_def, abi_decode_array_header_def,
    abi_decode_bulk_payload_def, abi_decode_copy_opcode_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def,
      abi_decoder_reentry_opcode_def]
QED

Theorem abi_decoder_typed_bulk_output_frame:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial /\
  run_inst_seq (emitted_insts st st') initial = OK t ==>
  abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial t
Proof
  strip_tac >> drule_all abi_decoder_bulk_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bulk_sequence >> strip_tac >> gvs[Excl "enc_def"] >>
  irule abi_decode_frame_widen >>
  qexistsl_tac [`d`, `32 + LENGTH vs * type_memory_size tv`] >> simp[]
QED

Theorem abi_decoder_typed_bulk_fields:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial ==>
  ?t. run_inst_seq (emitted_insts st st') initial = OK t /\
    abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) st' d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial t /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_decoder_typed_bulk_sequence >> strip_tac >>
  drule_all abi_decoder_typed_bulk_output_frame >> strip_tac >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_typed_bulk_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) st' d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      t.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_bulk_fields >> strip_tac >> qexists_tac `t` >>
  simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_bulk_execute:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\ fn_has_code st st' fn /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) st' d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decoder_budget first last b cap t /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  strip_tac >> drule_all abi_decoder_typed_bulk_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  `abi_decoder_budget first last b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_EXECUTE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI bulk decoder execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkExecute");
