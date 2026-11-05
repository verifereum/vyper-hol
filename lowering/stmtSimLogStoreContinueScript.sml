(* The store's write footprint is the sole mutable part of statement state. *)
Theory stmtSimLogStoreContinue
Ancestors
  stmtSimLogDataRun stmtSimLogDataFrame stmtSimLogAllocate stmtSimLogEncodeFrame
  stmtSimLogExecFields abiDecoderFrame compileEnv exprLoweringProps
  stmtSimLogEncodeFields exprSimBufferStore context emitHelper emitHelperProps
  stmtSimLogData stmtSimLogTopics stmtSimLogDataInput vyperABI supportedTypes stmtLowering venomInst venomState words list rich_list arithmetic

Theorem log_write_frame_fields:
  log_write_frame st b n s t ==>
  log_encode_external t = log_encode_external s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_footprint_frame [(b,n)] s t
Proof
  cheat
QED

Theorem log_write_frame_stmt:
  stmt_state_rel ctx func ce cx es s /\ log_write_frame st b n s t /\
  local_ptrs_reserved ce st /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    lo+sz <= b \/ b+n <= lo) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    off+type_memory_size tv <= b \/ b+n <= off) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  cheat
QED

Theorem log_store_scalar_safe[local]:
  supported_scalar_type ty /\ compile_store_memory ce src dst ty ty st = ((),final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_store_data_safe:
  !xs buf off st final. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data ce xs buf off st = ((),final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_store_data_memory_mono:
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

Theorem log_store_data_stmt:
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    lo+sz <= b+off \/ b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= lo) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b+off \/
    b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t avs. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx es t /\
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
      (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND xs))) (ListV avs)
      (b+off) (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) t.vs_memory /\
    log_data_layout cx (MAP SND xs) vs (b+off) t.vs_memory /\
    log_write_frame sa (b+off) (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s)
Proof
  cheat
QED
