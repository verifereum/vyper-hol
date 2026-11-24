(* The output-buffer supplier already exposes its counted physical run.
   Package that run as an observation of the same normalized endpoint. *)
Theory methodIdOutputBufferObserved
Ancestors bodyMemoryDefs[qualified,ignore_grammar]
  bodyFullBuiltinEnvMethodIdBuffer
  exprSimHash bodyFullLiteralBuffer bodyFullGhostFrame bodyFullUnwrapSlotPost
  exprSimPtrLiteralBuffer exprSimLiteralBuffer exprSimPtrLiteralOps
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  allocationPtr wordLoadStorePtr ptrSafetyTransport ptrDiscipline bodyPtrDefs
  fragGasSeqPtr instSeqPtrLo ghostPcTransportPtr exprLoweringProps vyperStorageFootprint
  builtinHashing context emitHelper exprSimProps loweringPosts
  loweringStateRelDefs venomState venomExecSemantics venomInst
  compileEnv words list finite_map

Theorem method_id_output_buffer_observed:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data,sd) /\
  emit_void MSTORE [data; value] sd = ((),sb) /\
  (!ann. builtin_result cx es.accounts ann MethodId tys vs = INL (BytesV bs)) /\
  LENGTH bs = 4 /\ TAKE 4 (word_to_bytes_be w) = bs /\
  eval_operand value s = SOME w /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s) /\
  op_taint tn value = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t z p q G' tn'.
    (?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
           z = (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand buf.buf_operand t = SOME p /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,64) /\
    w2n p + 64 < dimword (:256) /\
    val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n p) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes t n b sz ==>
      regions_disjoint (w2n p) 64 b sz) /\
    pure_frame cenv func es sa s t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    z = (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    lo <= w2n p /\ FLOOKUP G' q = SOME (w2n p,64) /\
    op_taint tn' buf.buf_operand = {} /\
    eval_operand buf.buf_operand z = SOME p /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n p,64) /\
    val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n p) z.vs_memory /\
    mem_word_at (w2n p) z.vs_memory = 4w /\
    mem_bytes_at (w2n p + 32) 4 z.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 64 ==> i NOTIN tn'.t_mem) /\
    (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n p) mem) /\
    ptr_mem_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) buf.buf_operand G' tn' z /\
    (!a len. a + len <= w2n p \/ w2n p + 64 <= a ==>
      mem_bytes_at a len z.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n p <= i /\ i < w2n p + 64} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ~z.vs_halted /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ return_buf_frame d cenv sb z /\
    ghost_kept_at lo cenv es sa G tn s G' tn' /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es z /\
      inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK z,G',tn') /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' z)
Proof
  strip_tac >> drule_all method_id_output_buffer_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`z`,`p`,`q`,`G'`,`tn'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac `t` >> simp[]
QED
