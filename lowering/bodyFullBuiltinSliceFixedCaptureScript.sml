(* A fixed-byte Slice captures its word in a fresh 32-byte allocation. *)
Theory bodyFullBuiltinSliceFixedCapture
Ancestors
  bodyFullAllocaFresh bodyFullBuiltinBytestringCopy wordLoadStorePtr
  fragGasOriginPtr fragExec loweringHalt emitHelperProps exprLoweringProps valueEncodingProps
  ptrDiscipline bodyPtrDefs allocaHistory freshWrites
  venomExecSemantics venomState venomInst compileEnv loweringStateRelDefs
  emitHelper context words list finite_map
  bodyFullSliceFixedCaptureObserved
  bodyFullHashKeccakFixed[qualified,ignore_grammar] exprSimAlloc[qualified,ignore_grammar]

Theorem slice_fixed_capture_full_run:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;src] sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  eval_operand src s = SOME w /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root p u t G' tn'.
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,G',tn')) /\
    t = mstore (w2n p) w u with vs_inst_idx := LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var root t = SOME p /\ ptr_covers G' tn' root t 32 /\
    mem_word_at (w2n p) t.vs_memory = w /\
    mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn'.t_mem) /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,32) /\
    w2n p+32 < dimword (:256) /\ w2n p+32 <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    u with <|vs_vars := s.vs_vars;vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next;vs_inst_idx := s.vs_inst_idx|> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func cenv cx es u) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n p) 32 b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n p) 32 b len) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!j. j < s.vs_alloca_next /\ j IN tn'.t_mem ==> j IN tn.t_mem)
Proof
  strip_tac >> drule_all slice_fixed_capture_observed >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`p`,`u`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`root`,`p`,`u`,`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[]
QED
