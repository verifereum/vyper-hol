Theory bodyFullAbiEncodeWordPack
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeFinish bodyFullAbiEncodeCopy
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  typedCopyOriginPtrBase[qualified,ignore_grammar]
  exprSimProps bodyFullAllocaFresh
  abiBuiltinAllocation entryDecodeStructure reasonCopySourcePtr decoderGhostFramePtr
  typedMemoryCopy valueEncodingProofs allocaHistory wordArgsPtr bodyMemoryDefs tupleMemoryFrame
  bodyFullUnwrapRun bodyPtrBytestringBuiltinsWindowGhost
  bodyPtrMakeArrayCopyStateFrame bodyPtrMakeArrayPrimitiveInstall
  stateRelProj exprSimStorageCopy exprSimAlloc venomMemDefs exprSimWordArgs
  abiBuiltinEncodeCode abiBuiltinEncodeMethod abiEncoderAppend abiEncoderMemory loweringHalt exprSimHash
  emitHelper emitHelperProps exprLoweringProps localPtrsProps freshWrites
  fragGasOriginPtrLoop fragExec compileEnv venomState venomExecSemantics venomInst finite_map words arithmetic
  pred_set list rich_list ptrDiscipline bodyPtrDefs loweringStateRelDefs loweringPosts
  bodyFullAbiEncodeWordPackData bodyFullAbiEncodeWordPackRun

Theorem abi_encode_word_pack_origin:
  lower_abi_encode mid 32
    (\dst. comp_ignore_bind (emit_void MSTORE [dst;value]) (comp_return (Lit 32w)))
    st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ local_ptrs_reserved ce origin /\ cs_extends origin st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand value s = SOME word /\ op_taint tn value = {} /\
  (!x. value = Var x ==> not_fresh_at st x) /\
  enc at av = word_to_bytes word T /\ LENGTH (enc at av) = 32 /\
  stmt_state_rel (Hentry:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame ce es ee origin s0 s /\
  ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
  ?p q t Gt tnt.
    out = Var q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tnt)) /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    eval_operand out t = SOME (n2w p) /\
    ptr_covers Gt tnt q t (32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (p,(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4)))) /\
    p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword(:256) /\
    (!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (32+(case mid of NONE => 0 | SOME _ => 4)) /\
      mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4)) 32 mem = enc at av /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)) /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
      stmt_state_rel H ctx func ce cx ee t) /\
    (!name b n. local_region ce ee.scopes t name b n ==>
      p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= b \/ b+n <= p) /\
    st.cs_next_id < final.cs_next_id /\
    (!H D. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
      ghost_inv_at D lo ret ce cx ee G tn s ==> ghost_inv_at D lo ret ce cx ee Gt tnt t) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gt tnt /\ wb_frame ce es ee origin s0 t /\
    (pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 t)
Proof
  pure_rewrite_tac[GSYM abi_word_pack_contract_eq] >>
  metis_tac[abi_encode_word_pack_run]
QED
