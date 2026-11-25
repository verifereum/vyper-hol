Theory createSizeImmutableLengthMods
Ancestors
  createSizeImmutableLength createExprSizeExitDefsMods
  exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper emitHelperProps
  bufferAllocationExecution abiBufferAllocationCode immutableCopyExecution
  loweringPosts loweringStateRelDefs stateRelProj loweringHalt freshWrites
  exprSimStorageCopy stmtReasonMemory venomState venomInst venomExecSemantics
  venomMemProps valueEncodingDefs valueEncodingProps vyperTyping vyperValue
  arithmetic words list finite_map abiDecodeStaticProps

(* The later stores do not affect the first word, even for a copy whose
   constructor source and destination overlap. *)

Theorem create_size_stmt_state_rel_immutable_frame_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE /\
  stmt_state_rel H ctx func cenv cx es s ==>
  immutable_frame_mods func cenv cx es s
Proof
  cheat
QED

Theorem create_snapshot_code_length_word_mods:
  vv_location vv = SOME LocCode /\
  stmt_state_rel H ctx func ce cx es s /\
  immutable_frame_mods func ce cx es s /\
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv es s /\
  read_result cx tv es = (INL (BytesV bytes),es) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  (ce.ce_is_ctor ==> !a. eval_operand (vv_operand vv) s = SOME a ==>
    val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bytes) (w2n a) s.vs_memory) /\
  copy_old_operand sa (vv_operand vv) /\ local_ptrs_reserved ce sa /\
  w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) /\
  emit_op MLOAD [snap] sb = (len,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  cheat
QED
