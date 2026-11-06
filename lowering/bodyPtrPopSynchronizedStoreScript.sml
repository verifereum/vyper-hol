Theory bodyPtrPopSynchronizedStore
Ancestors
  bodyPtrPopRegionStore stmtAppendStorageRunPtr fragGasSeqPtr
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst fragExec vyperStorage vfmState
Libs wordsLib

Theorem pop_emitted_storage_store_success:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME value ==>
  t = (if tr then tstore key value s else sstore key value s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  Cases_on `tr` >>
  gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def,
      eval_operands_def, exec_write2_def, AllCaseEqs()]
QED

Theorem pop_synchronized_header_store:
  lookup_storage header src = lookup_storage header dst ==>
  lookup_storage header (update_storage key value src) =
  lookup_storage header (update_storage key value dst)
Proof
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `header = key` >> simp[]
QED

Theorem pop_emitted_storage_store_backend:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME value ==>
  (if tr then contract_transient t else contract_storage t) =
    update_storage key value
      (if tr then contract_transient s else contract_storage s) /\
  (if tr then contract_storage t else contract_transient t) =
    (if tr then contract_storage s else contract_transient s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests
Proof
  strip_tac >> drule_all pop_emitted_storage_store_success >> strip_tac >>
  Cases_on `tr` >>
  gvs[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
      lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem pop_emitted_storage_store_observer:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME value /\
  bs + type_slot_size tv <= dimword (:256) /\
  (w2n key < bs \/ bs + type_slot_size tv <= w2n key) /\
  pop_region_taint_ok
    (if tr then contract_transient s else contract_storage s) bs tv X ==>
  pop_region_taint_ok
    (if tr then contract_transient t else contract_storage t) bs tv
    (key_update X key {})
Proof
  strip_tac >> drule_all pop_emitted_storage_store_backend >> strip_tac >>
  simp[] >> irule pop_region_taint_clean_store >> simp[]
QED

Theorem pop_emitted_storage_store_header:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME value /\
  lookup_storage header src = lookup_storage header
    (if tr then contract_transient s else contract_storage s) ==>
  lookup_storage header (update_storage key value src) =
  lookup_storage header (if tr then contract_transient t else contract_storage t)
Proof
  strip_tac >> drule_all pop_emitted_storage_store_backend >> strip_tac >>
  simp[] >> irule pop_synchronized_header_store >> simp[]
QED

Theorem pop_emitted_storage_store_path:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME value /\
  op_taint tn a = {} /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (if tr then tn with t_trans := key_update tn.t_trans key {}
     else tn with t_stor := key_update tn.t_stor key {})
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
   t.vs_requests = s.vs_requests` by
    (drule_all pop_emitted_storage_store_backend >> simp[]) >>
  drule_all emit_storage_store_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
     Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
