(* Physical output-buffer endpoint shared by both MethodId hash routes. *)
Theory bodyMethodIdOutputBufferMods
Ancestors
  bodyFullBuiltinEnvMethodIdBuffer bodyMemBiMethodIdSuffix bodyFullUnwrapRun
  exprSimHash exprSimLiteralBuffer exprSimPtrLiteralBuffer exprLoweringProps
  bufferAllocationExecution emitHelperProps allocaFootprint freshWrites
  bodyMemoryDefs bodyPtrDefs instSeqPtrLo memSafeRun stateRelProj stmtReasonMemory
  fragExec fragExecMem loweringPosts loweringStateRelDefs
  ptrDiscipline vyperStorageFootprint vyperStorageTrace compileEnv context
  venomState venomInst words list finite_map pred_set

Theorem method_id_output_code[local]:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data,sd) /\
  emit_void MSTORE [data; value] sd = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
            ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  (!pre i post u. emitted_insts sa sb = pre ++ i::post ==>
     unitTransformDefs$dalloca_no_wrap i u)
Proof
  strip_tac >> drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_void MSTORE _ sd = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  drule emit_op_extends >> strip_tac >>
  qpat_assum `emit_void MSTORE _ sd = _` (strip_assume_tac o MATCH_MP emit_void_extends) >>
  `emitted_insts sm sb = emitted_insts sm sh ++ emitted_insts sh sd ++ emitted_insts sd sb` by
    (qspecl_then [`sm`, `sh`, `sd`, `sb`] mp_tac emitted_insts_three >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)` by simp[mk_inst_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `!pre i post u. emitted_insts sa sb = pre ++ i::post ==>
     unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
     qpat_assum `emitted_insts sa sb = pre ++ i::post` (fn th => rewrite_tac[th]) >>
     simp[EVERY_APPEND]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[APPEND_ASSOC, mk_inst_def, is_terminator_def]
QED

Theorem method_id_output_allocation[local]:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data,sd) /\
  emit_void MSTORE [data; value] sd = ((),sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  eval_operand value s = SOME w /\ (!x. value = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  !aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule_all hash_method_id_output_alloca_code >> strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all (Q.INST [`sz` |-> `64`] (SPEC_ALL alloc_buffer_frame_run)) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  rename1 `eval_operand buf.buf_operand u = SOME a` >>
  drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  `eval_operand value u = SOME w` by (Cases_on `value` >> fs[eval_operand_def]) >>
  `!x. value = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `w2n a + 32 < dimword (:256)` by decide_tac >>
  `eval_operand buf.buf_operand u = SOME (n2w (w2n a))` by simp[] >>
  drule_all (Q.INST [`n` |-> `4`] hash_single_word_buffer_run) >> strip_tac >>
  drule_all method_id_output_code >> strip_tac >>
  `t' = t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
     qpat_assum `emitted_insts sa sb = _ ++ _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = u` (mp_tac o AP_TERM ``venom_state_vs_allocas``) >> simp[]) >>
  drule compile_alloc_buffer_execution >> disch_then (qspec_then `s` strip_assume_tac) >>
  `u.vs_allocas = (buffer_allocation_fields s sa.cs_next_id (w2n (64w:256 word))).vs_allocas` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK (update_var _ _ _)` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  simp[buffer_allocation_fields_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> simp[]
QED

Theorem method_id_output_buffer_scratch_run:
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
    ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t z p q G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    z = (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    buf.buf_operand = Var q /\ not_fresh_at sb q /\
    lo <= w2n p /\ w2n p + 64 < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) (fn_insts func) /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n p,64) /\
    FLOOKUP G' q = SOME (w2n p,64) /\ op_taint tn' buf.buf_operand = {} /\
    eval_operand buf.buf_operand z = SOME p /\
    val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n p) z.vs_memory /\
    mem_word_at (w2n p) z.vs_memory = 4w /\
    mem_bytes_at (w2n p + 32) 4 z.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 64 ==> i NOTIN tn'.t_mem) /\
    (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) (w2n p) mem) /\
    ptr_mem_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) buf.buf_operand G' tn' z /\
    (!a len. a + len <= w2n p \/ w2n p + 64 <= a ==>
      mem_bytes_at a len z.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid b n. FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
    tn'.t_mem SUBSET tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    z.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    ~z.vs_halted /\ alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ return_buf_frame d cenv sb z /\
    sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es z /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
      ghost_inv_at (DF H) 0 d cenv cx es G' tn' z)
Proof
  strip_tac >>
  drule_all (Q.INST [`lo` |-> `0`] method_id_output_buffer_full_run) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all method_id_output_code >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s`
    (drule_then assume_tac) >>
  drule_all method_id_output_buffer_mem_ok_unrestricted >> strip_tac >>
  `!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
     FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b` by
    (rpt gen_tac >> strip_tac >> drule_all method_id_output_allocation >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_data_section >> strip_tac >>
  drule run_inst_seq_memory_length >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) (fn_insts func)` by
    (drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
     drule_all hash_method_id_output_alloca_code >> fs[]) >>
  `lo <= w2n p` by
    (qpat_assum `!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==> _`
       (drule_then strip_assume_tac)
     >- (qpat_assum `allocas_from lo s`
           (qspecl_then [`sa.cs_next_id`,`w2n p`,`64`] mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
     decide_tac) >>
  `tn'.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
       (irule inst_seq_ptr_zero_to_lo >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexists_tac `DF H` >>
        qpat_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _`
          (fn th => simp_tac std_ss [th,SUBSET_REFL])) >>
     qpat_assum `z = _` SUBST1_TAC >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!pre i post u. emitted_insts sa sb = _ ==> _`
       (qspecl_then [`pre`,`i`,`post`,`u`] mp_tac) >>
     qpat_assum `emitted_insts sa sb = pre ++ i::post`
       (fn th => simp_tac std_ss [th])) >>
  qexistsl_tac [`t`,`z`,`p`,`q`,`G'`,`tn'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >> rpt conj_tac
      >- (qpat_assum `z = _` SUBST1_TAC >> simp[lookup_var_def] >>
          qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _`
            (drule_then (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])))
      >> qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G' x = _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `z = _` SUBST1_TAC >> simp[])
  >- (qpat_assum `z = _` SUBST1_TAC >> simp[])
  >- (qpat_assum `z = _` SUBST1_TAC >> simp[])
  >- (qpat_assum `z = _` SUBST1_TAC >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
