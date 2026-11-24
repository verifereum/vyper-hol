(* Constructor payload allocation for nonraw blueprint creation. *)
Theory createCtorBlueprintEntryMods
Ancestors
  createCtorBlueprintEntry createExprSizeExitDefsMods
  bodyFullAllocaFresh bodyFullExtCallDirectState bodyFullHashKeccakFixed
  abiBufferAllocationCode exprSimAlloc externalReturnFootprint stateRelProj
  exprSimProps exprLoweringProps fragGasOriginPtr fragGasOrigin fragExec
  bodyPtrDefs loweringPosts loweringStateRelDefs ptrDiscipline
  venomMemDefs venomState venomInst venomExecSemantics frameGasEvents
  compileEnv context finite_map arithmetic list words
Libs horizonTypeLib

Theorem ctor_encoder_blueprint_entry_mods:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?root pbase u Gu tu inst.
    buf.buf_operand = Var root /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root root 0 [] a u Gu tu /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!ms v. gas_origin_edge F explicit ctx func s ms (OK v) ==> ms = [] /\ v = u)
Proof
  cheat
QED
