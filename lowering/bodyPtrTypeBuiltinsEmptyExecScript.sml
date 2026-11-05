Theory bodyPtrTypeBuiltinsEmptyExec
Ancestors
  bodyPtrTypeBuiltinsEmptyWords bodyPtrTypeBuiltinsEmptyAlloc
  bodyPtrTypeBuiltinsEmptyZero bodyPtrTypeBuiltinsSeq
  builtinSimple emitHelper emitHelperProps exprSimBufferEmptyExec
  compileEnv context venomInst list exprLoweringProps abiEmptySequence rich_list
  fragExec fragGasSeqPtr fragGasPathPtr venomState

(* The semantic theory's decomposition is local, so expose this boundary
   for the checked execution port. *)
Theorem empty_buffer_compile_decompose:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    ?sm. compile_alloc_buffer sz sa = (buf,sm) /\
      (if header then emit_void MSTORE [buf.buf_operand; Lit 0w]
       else compile_zero_words buf.buf_operand ((sz+31) DIV 32)) sm = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
  simp[] >> Cases_on `header` >> simp[comp_bind_def, comp_ignore_bind_def,
                                     comp_return_def] >>
  pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
  strip_tac >> gvs[] >> qexists_tac `sm` >> simp[]
QED

Theorem empty_zero_words_no_gas:
  !n pop sa sb. compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_zero_words pop n sa` >>
  rename1 `compile_zero_words pop n sa = (unit_result,sm)` >>
  Cases_on `unit_result` >>
  drule_all empty_zero_words_successor_code >> disch_then SUBST1_TAC >>
  simp[mk_inst_def] >> first_x_assum irule >>
  qexists_tac `pop` >> simp[]
QED

Theorem empty_buffer_no_gas:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >> drule empty_buffer_compile_decompose >> strip_tac >>
  Cases_on `header` >> gvs[]
  >- (gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
      simp[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule empty_zero_words_no_gas >> strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  qpat_x_assum `inst_extends _ _` mp_tac >>
  simp[inst_extends_def] >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, EVERY_APPEND,
                   EVERY_DEF, mk_inst_def] >> gvs[mk_inst_def]
QED

Theorem empty_buffer_checked_path:
  !sz header sa sb buf func s t G tn H th D ctx PG.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_ptr D 0 ctx func PG G tn s 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  drule empty_buffer_no_gas >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    suspend "code" >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND] >> simp[]) >> simp[]
QED
Resume empty_buffer_checked_path[code]:
  fs[fn_has_code_def] >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
  simp[DROP_APPEND1, IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED
Finalise empty_buffer_checked_path
