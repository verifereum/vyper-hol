(* Runtime MethodId output buffer: one endpoint for all storage horizons. *)
Theory bodyFullBuiltinEnvMethodIdBuffer
Ancestors bodyMemoryDefs[qualified,ignore_grammar]
  exprSimHash bodyFullLiteralBuffer bodyFullGhostFrame bodyFullUnwrapSlotPost
  exprSimPtrLiteralBuffer exprSimLiteralBuffer exprSimPtrLiteralOps
  allocationPtr wordLoadStorePtr ptrSafetyTransport ptrDiscipline bodyPtrDefs
  fragGasSeqPtr instSeqPtrLo ghostPcTransportPtr exprLoweringProps vyperStorageFootprint
  builtinHashing context emitHelper exprSimProps loweringPosts
  loweringStateRelDefs venomState venomExecSemantics venomInst
  compileEnv words list finite_map

Theorem method_id_output_buffer_frame[local]:
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
    stmt_state_rel H ctx func cenv cx es s) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
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
      stmt_state_rel H ctx func cenv cx es t)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  first_assum (drule_then assume_tac) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (drule_all hash_method_id_output_alloca_code >> simp[]) >>
  `emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
   LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs` by simp[] >>
  drule_all hash_alloc_single_word_buffer_frame >>
  disch_then (qspec_then `4` strip_assume_tac) >>
  qexistsl_tac [`t`, `p`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qpat_x_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` kall_tac >>
  drule_all hash_alloc_single_word_buffer_frame >>
  disch_then (qspec_then `4` strip_assume_tac) >> gvs[]
QED

Theorem method_id_output_buffer_full_run:
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
  op_taint tn value = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t z p q G' tn'.
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
  strip_tac >>
  drule_all method_id_output_buffer_frame >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    metis_tac[] >>
  drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  rename1 `buf.buf_operand = Var q` >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) (fn_insts func)` by
    (drule_all hash_method_id_output_alloca_code >> simp[]) >>
  `64 < dimword (:256)` by simp[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by metis_tac[] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  rename1 `eval_operand buf.buf_operand u = SOME a` >>
  `?r. data = Var r /\ q <> r /\ ~not_fresh_at sa r /\
    (!x. value = Var x ==> x <> q /\ x <> r) /\
    emitted_insts sh sd = [mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]] /\
    emitted_insts sd sb = [mk_inst sd.cs_next_id MSTORE [Var r; value] []] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q];
       mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] [];
       mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r];
       mk_inst sd.cs_next_id MSTORE [Var r; value] []]` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [data; value] _ = _` mp_tac >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     gvs[not_fresh_at_def, rich_listTheory.DROP_APPEND] >> metis_tac[]) >>
  suspend "allocation_ghost"
QED

Resume method_id_output_buffer_full_run[allocation_ghost]:
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  `a = n2w b` by gvs[eval_operand_def] >>
  `eval_operand value u = SOME w` by
    (Cases_on `value` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `(!x. value = Var x ==> not_fresh_at sm x)` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[] >>
     gvs[not_fresh_at_def] >> metis_tac[]) >>
  `b + 32 < dimword (:256)` by decide_tac >>
  `eval_operand buf.buf_operand u = SOME (n2w b)` by metis_tac[] >>
  drule_all hash_single_word_buffer_run >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (simp[emitted_insts_def] >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [data; value] _ = _` mp_tac >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp[GSYM APPEND_ASSOC, rich_listTheory.DROP_APPEND]) >>
  `t' = t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
     qpat_x_assum `emitted_insts sa sb = _ ++ _`
       (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  `p = a` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  qabbrev_tac `G1 = G |+ (q,(b,64))` >>
  qabbrev_tac `tn1 = tn with <|t_var := tn.t_var |+ (q,{});
                                t_mem := tn.t_mem UNION dirty|>` >>
  qabbrev_tac `uh = mstore b 4w u` >>
  `lookup_var q u = SOME p` by metis_tac[] >>
  suspend "stores_ghost"
QED

Resume method_id_output_buffer_full_run[stores_ghost]:
  drule literal_mstore_ghost >>
  disch_then (qspecl_then [`4w`, `tn1`, `sm.cs_next_id`, `PG`, `G1`]
    strip_assume_tac) >>
  `w2n p = b` by simp[Once EQ_SYM_EQ, w2n_n2w] >>
  qabbrev_tac `tn2 = tn1 with t_mem := tn1.t_mem DIFF
    {i | b <= i /\ i < b + 32}` >>
  `step_prov PG G1 (mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] []) uh = G1 /\
   step_taint (mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] []) u uh tn1 = tn2` by
    gvs[Abbr `uh`, Abbr `tn2`] >>
  qabbrev_tac `ud = update_var r (n2w (b+32)) uh` >>
  qabbrev_tac `G2 = G1 |+ (r,(b,64))` >>
  qabbrev_tac `tn3 = tn2 with t_var := tn2.t_var |+ (r,{})` >>
  `FLOOKUP G1 q = SOME (b,64)` by simp[Abbr `G1`, FLOOKUP_UPDATE] >>
  `step_prov PG G1 (mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]) ud = G2 /\
   step_taint (mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]) uh ud tn2 = tn3` by
    (drule literal_add_ghost >>
     simp[Abbr `ud`, Abbr `G2`, Abbr `tn3`] >>
     metis_tac[]) >>
  `lookup_var r ud = SOME (n2w (b+32)) /\
   eval_operand value ud = SOME w /\ op_taint tn3 value = {}` by
    (Cases_on `value` >>
     gvs[Abbr `ud`, Abbr `uh`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
         eval_operand_def, lookup_var_def, update_var_def,
         ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `uf = mstore (b+32) w ud` >>
  qabbrev_tac `tn4 = step_taint
    (mk_inst sd.cs_next_id MSTORE [Var r; value] []) ud uf tn3` >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G2`, `sd.cs_next_id`] mp_tac) >>
  simp[w2n_n2w, Abbr `uf`, GSYM markerTheory.Abbrev_def] >>
  strip_tac >>
  `tn4.t_imm = tn3.t_imm` by
    simp[Abbr `tn4`, ptrDisciplineTheory.step_taint_def,
         ptrDisciplineTheory.imm_taint_def, mk_inst_def] >>
  suspend "clean_taint"
QED

Resume method_id_output_buffer_full_run[clean_taint]:
  `tn4.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+64} /\
   tn4.t_stor = tn.t_stor /\ tn4.t_trans = tn.t_trans /\
   tn4.t_imm = tn.t_imm` by
    (simp[Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >>
     qpat_x_assum `dirty SUBSET _` mp_tac >>
     simp[pred_setTheory.EXTENSION, pred_setTheory.SUBSET_DEF] >>
     disch_tac >> gen_tac >>
     qpat_x_assum `!x. x IN dirty ==> _` (qspec_then `x` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `x IN dirty` >> Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  `ptr_covers G1 tn1 q u 32 /\
   ptr_covers G2 tn3 r ud 32` by
    (simp[bodyPtrDefsTheory.ptr_covers_def, Abbr `G1`, Abbr `G2`,
          Abbr `tn1`, Abbr `tn3`, Abbr `tn2`, Abbr `ud`,
          ptrDisciplineTheory.op_taint_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, w2n_n2w] >>
     gvs[lookup_var_def] >> decide_tac) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] []) u = OK uh /\
   step_inst_base (mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]) uh = OK ud /\
   step_inst_base (mk_inst sd.cs_next_id MSTORE [Var r; value] []) ud =
     OK (mstore (b+32) w ud)` by
    (qpat_x_assum `q = STRING _ _` kall_tac >>
     `lookup_var q uh = SOME (n2w b)` by
       simp[Abbr `uh`, lookup_var_def, mstore_def] >>
     conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
             eval_operand_def, Abbr `uh`, w2n_n2w] >>
     conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
             eval_operand_def, Abbr `ud`, wordsTheory.word_add_n2w] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w]) >>
  suspend "pointer_sequence"
QED

Resume method_id_output_buffer_full_run[pointer_sequence]:
  `!D. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q];
       mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] [];
       mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r];
       mk_inst sd.cs_next_id MSTORE [Var r; value] []] s G2 tn4` by
    (gen_tac >> qpat_x_assum `q = STRING _ _` kall_tac >>
     qpat_x_assum `sm.cs_next_id = _` kall_tac >>
     qpat_x_assum `sh.cs_next_id = _` kall_tac >>
     `~is_terminator (mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] []).inst_opcode /\
      ~is_terminator (mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]).inst_opcode /\
      ~is_terminator (mk_inst sd.cs_next_id MSTORE [Var r; value] []).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     pure_once_rewrite_tac [inst_seq_ptr_def] >>
     asm_simp_tac bool_ss [literal_alloca_ptr_inst_ok, exec_result_case_def] >>
     pure_once_rewrite_tac [inst_seq_ptr_def] >>
     conj_tac
     >- (irule literal_mstore_ptr_inst_ok >>
         simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
     asm_simp_tac bool_ss [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, exec_result_case_def,
       ghostPcTransportPtrTheory.step_prov_inst_idx,
       ghostPcTransportPtrTheory.step_taint_inst_idx] >>
     pure_once_rewrite_tac [inst_seq_ptr_def] >>
     conj_tac
     >- (irule literal_add_ptr_inst_ok >>
         simp[Abbr `tn2`, Abbr `tn1`, ptrDisciplineTheory.op_taint_def,
              FLOOKUP_UPDATE]) >>
     asm_simp_tac bool_ss [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, exec_result_case_def,
       ghostPcTransportPtrTheory.step_prov_inst_idx,
       ghostPcTransportPtrTheory.step_taint_inst_idx] >>
     pure_once_rewrite_tac [inst_seq_ptr_def] >>
     conj_tac
     >- (irule fragExecPtrTheory.ptr_inst_ok_mstore >>
         simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
     asm_simp_tac bool_ss [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, exec_result_case_def,
       ghostPcTransportPtrTheory.step_prov_inst_idx,
       ghostPcTransportPtrTheory.step_taint_inst_idx] >>
     simp[inst_seq_ptr_def, Abbr `tn4`]) >>
  suspend "execution_path"
QED

Resume method_id_output_buffer_full_run[execution_path]:
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_x_assum `!H. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G2 tn4` by
    (gen_tac >> qpat_x_assum `q = STRING _ _` kall_tac >>
     qpat_x_assum `emitted_insts sa sb = emitted_insts sa sm ++ _` kall_tac >>
     qpat_x_assum `sm.cs_next_id = _` kall_tac >>
     qpat_x_assum `sh.cs_next_id = _` kall_tac >>
     irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists `D` >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule emit_op_extends >> strip_tac >>
     qpat_assum `emit_void MSTORE [data; value] sd = _`
       (mp_tac o MATCH_MP emit_void_extends) >>
     strip_tac >> gvs[same_blocks_def] >>
     simp[GSYM APPEND_ASSOC]) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `q = STRING _ _` kall_tac >>
     qpat_x_assum `emitted_insts sa sb = emitted_insts sa sm ++ _` kall_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
       simp[mk_inst_def, is_terminator_def] >>
     `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
     simp[]) >>
  `b+64 <= u.vs_alloca_next` by
    (irule instMemFrontierTheory.alloca_region_below_frontier >>
     conj_tac >- gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     qexistsl_tac [`sa.cs_next_id`, `b`, `64`] >> simp[]) >>
  suspend "memory_safety"
QED

Resume method_id_output_buffer_full_run[memory_safety]:
  `inst_mem_below_frontier (mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] []) u /\
   inst_mem_below_frontier (mk_inst sd.cs_next_id MSTORE [Var r; value] []) ud` by
    (simp[instMemFrontierTheory.below_frontier_MSTORE,
          eval_operand_def, Abbr `ud`, Abbr `uh`, lookup_var_def,
          update_var_def, mstore_def, w2n_n2w] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qpat_x_assum `q = STRING _ _` kall_tac >>
     qpat_x_assum `emitted_insts sa sb = emitted_insts sa sm ++ _` kall_tac >>
     qpat_x_assum `sm.cs_next_id = _` kall_tac >>
     qpat_x_assum `sh.cs_next_id = _` kall_tac >>
     `inst_mem_below_frontier (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) s /\
      inst_mem_below_frontier (mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r]) uh` by
       (conj_tac >> irule instMemFrontierTheory.below_frontier_no_ranges >>
        simp[mk_inst_def]) >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_def, exec_result_case_def] >>
     simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G2,tn4)` by
    (gen_tac >>
     qpat_x_assum `q = STRING _ _` kall_tac >>
     qpat_x_assum `emitted_insts sa sb = emitted_insts sa sm ++ _` kall_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
     `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G2 tn4` by simp[] >>
     `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
       metis_tac[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[mk_inst_def]) >>
  suspend "exterior_frame"
QED

Resume method_id_output_buffer_full_run[exterior_frame]:
  `!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn4 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> q /\ x <> r` by metis_tac[] >>
     simp[Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
          ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!i. b <= i /\ i < b+64 ==> i NOTIN tn4.t_mem` by simp[] >>
  `ghost_kept_at lo cenv es sa G tn s G2 tn4` by
    (simp[bodyPtrDefsTheory.ghost_kept_at_def] >> rpt strip_tac >>
     gvs[] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn4.t_mem t.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) b mem` by
    (rpt strip_tac >> irule literal_clean_representation_robust >>
     conj_tac >- simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def] >>
     qexistsl_tac [`tn4.t_mem`, `t.vs_memory`] >>
     gvs[valueEncodingDefsTheory.val_wf_def, val_footprint_def, w2n_n2w]) >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs)
     buf.buf_operand G2 tn4 t` by
    (simp[bodyPtrDefsTheory.ptr_mem_ok_def, vyperValueTheory.evaluate_type_def] >>
     rpt strip_tac >>
     `p' = q` by metis_tac[operand_11] >>
     qexistsl_tac [`b`, `64`] >>
     simp[Abbr `G2`, Abbr `G1`, FLOOKUP_UPDATE, val_store_size_def,
          vfmConstantsTheory.word_size_def]) >>
  `!off len. off+len <= b \/ b+64 <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint b 64 off len` by
       (simp[regions_disjoint_def] >> decide_tac) >>
     `mem_bytes_at off len (mstore (b+32) w uh).vs_memory =
        mem_bytes_at off len uh.vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`b`, `64`] >> simp[]) >>
     `mem_bytes_at off len uh.vs_memory = mem_bytes_at off len u.vs_memory` by
       (qunabbrev_tac `uh` >> irule mstore_region_frame >>
        qexistsl_tac [`b`, `64`] >> simp[]) >> metis_tac[]) >>
  suspend "state_frame"
QED

Resume method_id_output_buffer_full_run[state_frame]:
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `t' with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp[venom_state_component_equality] >> gvs[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (irule step_inst_allocas_from >>
     qexistsl [`ctx`, `0`, `mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]`, `s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  `lo <= b` by
    (qpat_x_assum `allocas_from lo u`
       (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sa.cs_next_id`, `b`, `64`] mp_tac) >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (conj_tac
     >- (qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def]) >>
     simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (`u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
       (qpat_assum `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) s = OK u` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[step_inst_base_opcode_eqs,mk_inst_def,exec_alloca_def,
          AllCaseEqs(),update_var_def] >> rpt strip_tac >> gvs[]) >>
     qpat_assum `t' with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!n off sz. local_region cenv es.scopes s n off sz ==>
     b+64 <= off \/ off+sz <= b` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t n off sz` by
       (irule (Q.INST [`sa` |-> `sa`, `s0` |-> `s`]
         local_region_frame_fwd) >> simp[] >> metis_tac[]) >>
     qpat_assum `!n b' sz. local_region cenv es.scopes t n b' sz ==> _`
       drule >> simp[regions_disjoint_def] >> decide_tac) >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id MSTORE [Var q; Lit 4w] [];
     mk_inst sh.cs_next_id ADD [Var q; Lit 32w] [r];
     mk_inst sd.cs_next_id MSTORE [Var r; value] []]` by
    (qpat_x_assum `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb`
       mp_tac >> simp[]) >>
  suspend "horizon_frame"
QED

Resume method_id_output_buffer_full_run[horizon_frame]:
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G2 tn4 t` by
    (qx_gen_tac `H` >> strip_tac >>
     `ghost_inv_at (DF H) lo d cenv cx es G tn s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     `local_ptrs_rel func cenv es.scopes s` by gvs[stmt_state_rel_def,state_rel_def] >>
     `stor_taint_ok_at (DF H) tn4 t` by
       fs[ghost_inv_at_def, stor_taint_ok_at_def] >>
     irule (Q.INST [`nb` |-> `64`, `start` |-> `b`] unwrap_slot_copy_ghost_inv_at) >>
     simp[] >> qexistsl_tac [`G`, `b`, `func`, `s`, `sa`, `tn`] >>
     simp[] >> rpt strip_tac >> simp[] >> metis_tac[]) >>
  `p' = q` by
    (qpat_assum `buf.buf_operand = Var p'` mp_tac >>
     qpat_assum `buf.buf_operand = Var q` SUBST1_TAC >> simp[]) >>
  `lookup_var q t = SOME p` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t' = lookup_var x u`
       (qspec_then `q` mp_tac) >> fs[]) >>
  `p = n2w b` by
    (qpat_assum `w2n p = b` (fn th => rewrite_tac [GSYM th]) >> simp[]) >>
  `FLOOKUP t.vs_vars p' = SOME (n2w b)` by
    (qpat_assum `lookup_var q t = SOME p` mp_tac >>
     qpat_assum `p' = q` mp_tac >>
     qpat_assum `p = n2w b` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def]) >>
  `op_taint tn4 (Var q) = {}` by
    simp[Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.step_taint_def,
      ptrDisciplineTheory.set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, LET_THM] >>
  suspend "endpoint_frame"
QED

Resume method_id_output_buffer_full_run[endpoint_frame]:
  `sb.cs_next_var = sh.cs_next_var + 1` by
    (qpat_assum `emit_op ADD [buf.buf_operand; Lit 32w] sh = (data,sd)` mp_tac >>
     qpat_assum `emit_void MSTORE [data; value] sd = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `not_fresh_at sb q` by
    (irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sh` >> simp[]) >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [q]) s = OK u`
       mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def,
       exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def]) >>
  `t.vs_halted = u.vs_halted /\ t.vs_current_bb = u.vs_current_bb` by
    (qpat_assum `t' with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `~t.vs_halted /\ s.vs_alloca_next <= t.vs_alloca_next /\
   t.vs_current_bb = sb.cs_current_bb` by simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by simp[] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `return_buf_frame d cenv sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    ((irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     goal_assum (drule_at Any) >>
     simp[lookup_var_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s`
       (qspec_then `x` (mp_tac o REWRITE_RULE [lookup_var_def])) >> simp[] >> (metis_tac[lookup_var_def, bodyMemoryDefsTheory.return_buf_frame_frame]))) >>
  suspend "endpoint_post"
QED

Resume method_id_output_buffer_full_run[endpoint_post]:
  qpat_x_assum `(p':string) = q` SUBST_ALL_TAC >>
  qpat_x_assum `w2n p = b` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `p = n2w (w2n p)` kall_tac >>
  `FLOOKUP t.vs_vars q = SOME p` by
    (qpat_assum `lookup_var q t = SOME p`
      (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
  `mem_word_at (w2n p) t.vs_memory = 4w /\
   mem_bytes_at (w2n p+32) 4 t.vs_memory = bs` by
    (qpat_assum `val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs)
       (w2n p) t.vs_memory`
       (mp_tac o REWRITE_RULE [valueEncodingDefsTheory.val_in_memory_def]) >>
     qpat_assum `LENGTH bs = 4` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) (Var q)
     G2 tn4 (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `ptr_mem_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs)
       buf.buf_operand G2 tn4 t` mp_tac >>
     qpat_assum `buf.buf_operand = Var q` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_mem_ok_def, lookup_var_def, eval_operand_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G2 tn4 /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G2,tn4) /\
    ghost_inv_at (DF H) lo d cenv cx es G2 tn4
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qx_gen_tac `H` >> strip_tac >> rpt conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t`
           (qspec_then `H` mp_tac) >> simp[stmt_state_rel_inst_idx])
     >- simp[]
     >- simp[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ G2 tn4 t`
       (qspec_then `H` mp_tac) >>
     simp[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx]) >>
  suspend "package"
QED

Resume method_id_output_buffer_full_run[package]:
  qexistsl_tac [`p`,`G2`,`tn4`] >>
  simp_tac std_ss [eval_operand_def] >>
  rpt conj_tac >> rpt (first_assum ACCEPT_TAC)
  >- (qpat_assum `Abbrev (G2 = _)` mp_tac >>
      qpat_assum `FLOOKUP G1 q = _` mp_tac >>
      qpat_assum `q <> r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[markerTheory.Abbrev_def, FLOOKUP_UPDATE]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    mp_tac >>
  qpat_assum `emitted_insts sa sb = emitted_insts sa sm ++ _` mp_tac >>
  qpat_assum `emitted_insts sa sm = _` mp_tac >>
  qpat_assum `q = STRING _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Finalise method_id_output_buffer_full_run
