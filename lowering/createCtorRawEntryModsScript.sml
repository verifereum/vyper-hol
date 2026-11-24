Theory createCtorRawEntryMods
Ancestors
  createCtorRawEntry createExprSizeExitDefsMods
  bodyFullExtCallDirectState bodyFullMemoryFrames bodyFullAbiEncodeCopy
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  abiEncoderWindowLeaves abiEncoderWindowPhase typedCopyOriginPtrBase
  abiBuiltinAllocation emitHelperProps fragGasOrigin fragExec context
  gasEventsFuel exprLoweringProps venomMemDefs abiEncoderWindowContract
  venomExecSemantics venomState venomInst words
  list arithmetic finite_map pred_set createCtorBlueprintEntryMods
  bodyFullStoreSlotsAddresses abiDecodePtrBytesTail abiEncoderWindowSequence ptrDiscipline bodyPtrDefs
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedArrayBody ghostPcTransportPtr
  loweringPosts freshWrites assignTuplePtrCopyLen memoryReadProps
  fragGasOriginPtr exprSimProps

(* Each instruction in the raw prologue is nonterminating and is not an
   INVOKE.  The supplied origin edge therefore fixes its result. *)

Theorem ctor_raw_destination_actual_mods:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst,c) /\
  fn_has_code b c func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\ w2n n <= capacity /\
  not_fresh_at se src /\ not_fresh_at se len /\
  lookup_var src s = SOME p /\ lookup_var len s = SOME n /\
  ptr_covers G tn src s (w2n n) /\ op_taint tn (Var len) = {} /\
  w2n p + w2n n <= s.vs_alloca_next /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK u) /\
  gas_origin_edge F explicit ctx func u bm (OK t) /\
  gas_origin_edge F explicit ctx func t cm (OK v) ==>
  ?root pbase out Gv tv inst.
    buf.buf_operand = Var root /\ dst = Var out /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root out (w2n n) [] c v Gv tv /\
    pure_frame ce func ee se s v /\
    (!x. not_fresh_at se x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gv,tv))
Proof
  cheat
QED
