(* Actual-site resources at the nonbulk source-array constructor boundary. *)
Theory sourceOwnedArrayConstructorPtr
Ancestors
  sourceOwnedArrayLoopPtr decoderArrayInitPtr physicalArrayInitSequence
  actualAllocaReplayPtr abiDecoderRecursiveArray abiDecoderRecursiveLoopLayout
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard ctorAbiActualAlloc
  emitHelperProps emitHelper exprLowering exprLoweringProps abiDecoderContract
  rich_list context compileEnv venomState venomInst
  venomExecSemantics venomMemDefs venomWf finite_map words list arithmetic

(* Initialization writes only its own registers, so freshness at the eventual
   decoder limit is preserved, not merely freshness at the initializer limit. *)
Theorem array_loop_init_future_fresh:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz sa = (setup,sb) /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  fresh_vars_wrt limit t
Proof
  strip_tac >>
  `!n. sb.cs_next_var <= n ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\
      ~MEM (STRING #"%" (toString n)) i.inst_outputs)
      (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `abi_decode_source_opcode opc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `hi = Lit 0w` >>
     simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
       abi_decode_dynarray_end_def, abi_decode_le_guard_def,
       abi_decode_array_header_def, abi_decode_index_init_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     rpt strip_tac >>
     gvs[] >>
     pure_rewrite_tac [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
     simp_tac std_ss [DROP_LENGTH_APPEND] >>
     fs[abi_decode_source_opcode_def] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `!n. limit.cs_next_var <= n ==>
    lookup_var (STRING #"%" (toString n)) t =
    lookup_var (STRING #"%" (toString n)) s` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     goal_assum (drule_at Any) >> first_x_assum irule >> decide_tac) >>
  fs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >> gvs[]
QED

