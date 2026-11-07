Theory exprSimAbiDecodeSetupExec
Ancestors
  abiBuiltinDecodeSetup abiDecoderCode abiDecoderContract builtinAbi compileEnv arithmetic pair
  exprSimAbiDecodePrefixExec opcodeClass venomInstProofs venomExecProofs
  venomInst venomExecSemantics fragExec exprLoweringProps list rich_list
  abiBuiltinDecodeHeader abiBuiltinAllocation abiDecoderBytesPrefix emitHelperProps
  venomState finite_map words abiDecoderReentry abiDecoderAppend

Theorem abi_decode_output_site_interval:
  lower_abi_decode data info min_size max_size outsz start = (result,final) ==>
  start.cs_next_id <= abi_builtin_decode_output_site start min_size max_size /\
  abi_builtin_decode_output_site start min_size max_size < final.cs_next_id
Proof
  strip_tac >> drule lower_abi_decode_bounded_setup >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  Cases_on `decoded` >>
  drule abi_decoder_to_buf_code >>
  simp[abi_decode_source_opcode_def] >>
  simp[abi_decoder_code_def] >> strip_tac >>
  gvs[abi_builtin_decode_output_site_def]
QED

Theorem abi_decode_setup_step_envelope[local]:
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
  (!v z. step_inst_base i v <> Halt z) /\
  (!v z. step_inst_base i v = OK z ==> z.vs_current_bb = v.vs_current_bb)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> drule step_inst_base_halt_opcodes >>
      strip_tac >> gvs[is_terminator_def]) >>
  rpt strip_tac >>
  `step_inst 0 ARB i v = OK z` by simp[step_inst_non_invoke] >>
  drule step_preserves_control_flow >> simp[]
QED

Theorem abi_decode_setup_run_inversion:
  abi_builtin_decode_setup data min_size max_size outsz start = (ops,ready) /\
  fn_has_code start ready fn /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  run_from fuel ctx fn s = Halt h ==>
  ?a. run_inst_seq (emitted_insts start ready) s = OK a /\
    run_from fuel ctx fn
      (a with vs_inst_idx := LENGTH ready.cs_current_insts) = Halt h
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  fs[fn_has_code_def] >>
  `ready.cs_current_insts = start.cs_current_insts ++ emitted_insts start ready` by
    metis_tac[prefix_drop_equiv, emitted_insts_def] >>
  `?rest. bb.bb_instructions = ready.cs_current_insts ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `LENGTH ready.cs_current_insts =
     LENGTH (start.cs_current_insts ++ emitted_insts start ready)` by metis_tac[] >>
  pop_assum SUBST1_TAC >>
  irule abi_decode_setup_prefix_inversion >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[abi_decode_setup_step_envelope]
QED

Theorem abi_decode_setup_run_split:
  abi_builtin_decode_setup data min_size max_size outsz start = (ops,ready) /\
  run_inst_seq (emitted_insts start ready) s = OK a ==>
  ?inputs header buf u.
    abi_builtin_decode_header data min_size max_size start = (inputs,header) /\
    compile_alloc_buffer outsz header = (buf,ready) /\
    ops = (buf.buf_operand,SND inputs,FST inputs) /\
    run_inst_seq (emitted_insts start header) s = OK u /\
    run_inst_seq (emitted_insts header ready) u = OK a /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `header_st.cs_current_insts = start.cs_current_insts ++ emitted_insts start header_st` by
    metis_tac[prefix_drop_equiv, emitted_insts_def] >>
  `emitted_insts start ready =
     emitted_insts start header_st ++ emitted_insts header_st ready` by
    (irule emitted_insts_append >> simp[]) >>
  `?u. run_inst_seq (emitted_insts start header_st) s = OK u` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts header_st ready` mp_tac) >>
     metis_tac[]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts header_st ready` assume_tac) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_nonallocating_sequence_frame >>
     qexists_tac `emitted_insts start header_st` >> simp[] >> fs[EVERY_MEM]) >>
  qexistsl_tac [`inputs`, `header_st`, `buf`, `u`] >> metis_tac[]
QED

Theorem abi_decode_alloc_buffer_run_result:
  compile_alloc_buffer outsz st = (buf,ready) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (d,outsz)) /\
  outsz < dimword (:256) /\
  run_inst_seq (emitted_insts st ready) s = OK a ==>
  eval_operand buf.buf_operand a = SOME (n2w d) /\
  FLOOKUP a.vs_allocas st.cs_next_id = SOME (d,outsz)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK a` mp_tac >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    eval_operand_def, exec_alloca_def, w2n_n2w] >>
  rpt strip_tac >> gvs[update_var_def, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE]
QED

Theorem abi_decode_setup_run_output:
  abi_builtin_decode_setup data min_size max_size outsz start = (ops,ready) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
      SOME (d,outsz)) /\
  outsz < dimword (:256) /\
  run_inst_seq (emitted_insts start ready) s = OK a ==>
  eval_operand (FST ops) a = SOME (n2w d) /\
  FLOOKUP a.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
    SOME (d,outsz) /\
  abi_decoder_operand_live ready.cs_next_var (FST ops)
Proof
  strip_tac >> drule_all abi_decode_setup_run_split >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  `header.cs_next_id = abi_builtin_decode_output_site start min_size max_size` by
    simp[abi_builtin_decode_output_site_def] >>
  `eval_operand buf.buf_operand a = SOME (n2w d) /\
   FLOOKUP a.vs_allocas header.cs_next_id = SOME (d,outsz)` by
    (irule abi_decode_alloc_buffer_run_result >>
     simp[] >> qexists_tac `u` >> simp[]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule abi_decoder_operand_live_emit >> metis_tac[FST]
QED

Theorem abi_decode_lower_setup_execution:
  lower_abi_decode data info min_size max_size outsz start = (result,final) /\
  fn_has_code start final fn /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  run_from fuel ctx fn s = Halt h ==>
  ?ops ready a.
    abi_builtin_decode_setup data min_size max_size outsz start = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (Lit 0w) MLOAD
      (FST (SND ops)) (SND (SND ops)) info ready = ((),final) /\
    result = FST ops /\ cs_extends ready final /\
    run_inst_seq (emitted_insts start ready) s = OK a /\
    run_from fuel ctx fn
      (a with vs_inst_idx := LENGTH ready.cs_current_insts) = Halt h
Proof
  strip_tac >> drule lower_abi_decode_bounded_setup >> strip_tac >>
  Cases_on `decoded` >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends start ready` by
    (simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends ready final` by
    (mp_tac (cj 1 cs_appends_abi_decode_mutual) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `fn_has_code start ready fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_decode_setup_run_inversion >> strip_tac >>
  qexistsl_tac [`ops`, `ready`, `a`] >> simp[]
QED

Theorem abi_decode_lower_setup_output:
  lower_abi_decode data info min_size max_size outsz start = (result,final) /\
  fn_has_code start final fn /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  run_from fuel ctx fn s = Halt h /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
      SOME (d,outsz)) /\ outsz < dimword (:256) ==>
  ?ops ready a.
    abi_builtin_decode_setup data min_size max_size outsz start = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (Lit 0w) MLOAD
      (FST (SND ops)) (SND (SND ops)) info ready = ((),final) /\
    result = FST ops /\ cs_extends ready final /\
    run_inst_seq (emitted_insts start ready) s = OK a /\
    run_from fuel ctx fn
      (a with vs_inst_idx := LENGTH ready.cs_current_insts) = Halt h /\
    eval_operand result a = SOME (n2w d) /\
    FLOOKUP a.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
      SOME (d,outsz) /\
    abi_decoder_operand_live ready.cs_next_var result
Proof
  strip_tac >> drule_all abi_decode_lower_setup_execution >> strip_tac >>
  `eval_operand (FST ops) a = SOME (n2w d) /\
   FLOOKUP a.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
     SOME (d,outsz) /\ abi_decoder_operand_live ready.cs_next_var (FST ops)` by
    (irule abi_decode_setup_run_output >>
     simp[] >> conj_tac >- metis_tac[] >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`ops`, `ready`, `a`] >> simp[]
QED
