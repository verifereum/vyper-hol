Theory bodyMemBiBlockHashPath
Ancestors
  bodyUnopFragMemory builtinProps builtinSimple builtinMisc fragGasFresh fragGasSeqMem
  allocaHistoryFragment instMemFrontier memSafeRun fragExec fragExecMem varsExt fragGasMode
  compileEnv loweringStateRelDefs exprLoweringProps exprSimProps venomInstProofs emitHelper
  exprSimDefs finite_map
  list rich_list arithmetic venomInst venomExecSemantics venomState

Theorem blockhash_path_opcodes:
  compile_blockhash x sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule compile_blockhash_outputs >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  rpt strip_tac >> gvs[is_terminator_def, is_ext_call_op_def]
QED

Theorem blockhash_mem_ok:
  compile_blockhash x sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  drule compile_blockhash_outputs >> simp[EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> rpt strip_tac >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem blockhash_gas_count:
  compile_blockhash x sa = (op,sb) ==>
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0
Proof
  strip_tac >> drule blockhash_path_opcodes >>
  simp[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]
QED

Theorem blockhash_code_prefix:
  compile_blockhash x sa = (op,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule compile_blockhash_shape >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
  simp[DROP_APPEND]
QED

Theorem blockhash_clean_run:
  compile_blockhash x sa = (op,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)
Proof
  strip_tac >> drule blockhash_path_opcodes >> strip_tac >>
  irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  fs[EVERY_MEM]
QED

Theorem blockhash_clean_abort_path_mem:
  compile_blockhash x sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = Abort a t0 ==>
  ?t j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule blockhash_clean_run >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >>
  qpat_x_assum `run_inst_seq _ (drop_fresh _ _) = _` kall_tac >>
  drule_all blockhash_code_prefix >> strip_tac >>
  drule blockhash_path_opcodes >> strip_tac >>
  drule blockhash_mem_ok >> disch_then (qspec_then `s` assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> metis_tac[]
QED

Theorem blockhash_clean_success_path_mem:
  compile_blockhash x sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ vars_ext t0 t /\
      gas_marked_path T ctx func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule blockhash_clean_run >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >>
  qpat_x_assum `run_inst_seq _ (drop_fresh _ _) = _` kall_tac >>
  drule_all blockhash_code_prefix >> strip_tac >>
  drule blockhash_path_opcodes >> strip_tac >>
  drule blockhash_mem_ok >> disch_then (qspec_then `s` assume_tac) >>
  drule blockhash_gas_count >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >>
  simp[gas_marked_path_def] >> metis_tac[]
QED

Theorem blockhash_extends:
  compile_blockhash x sa = (op,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule compile_blockhash_shape >> strip_tac >>
  simp[cs_extends_def] >> qexists_tac `[]` >> simp[]
QED

Theorem blockhash_next_var:
  compile_blockhash x sa = (op,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem blockhash_run_post:
  compile_blockhash x sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  vars_ext t0 t /\ eval_operand op t0 = SOME w ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w /\
  (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
     lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME v) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
     FLOOKUP (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas aid = SOME b) /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory = s.vs_memory /\
  ~(t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_blockhash_frame >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  `eval_operand op t = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = t0 with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[lookup_var_def]) >>
  qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem blockhash_run_history:
  compile_blockhash x sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all blockhash_code_prefix >> strip_tac >>
  drule blockhash_path_opcodes >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    fs[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED
