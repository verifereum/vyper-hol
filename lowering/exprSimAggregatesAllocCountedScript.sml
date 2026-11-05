(*
 * Counted buffer allocation of aggregate literals (#636)
 *
 * The gas-counted form of exprSimAggregateChildren's buffer_alloc_frag:
 * the buffer's ALLOCA as a counted path that reads no gas.
 *
 * TOP-LEVEL:
 *   buffer_alloc_counted
 *)
Theory exprSimAggregatesAllocCounted
Ancestors
  exprSimAggregateLoops exprSimAggregateChildren exprSimAlloc
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq fragExec
  exprLowering exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState

(* The buffer's ALLOCA, counted: one instruction that reads no gas. *)
Theorem buffer_alloc_counted:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?inst x t b. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path F ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid p n. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n <=>
      local_region ce es.scopes s0 name p n)
Proof
  cheat
QED
