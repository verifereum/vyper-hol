(* Separated scratch write and final RawLog expression frame. *)
Theory bodyFullRawLogFixedTailFrame
Ancestors
  rawLogCoreFrame actualAllocExec exprSimAlloc exprSimProps
  bodySimFull bodyPtrDefs valueEncodingProps loweringPosts exprLoweringProps
  stmtSimDefs allocaHistory emitHelper compileEnv context loweringStateRelDefs
  vyperStorageFootprint vyperStorageBackend venomState venomInst
  words list rich_list finite_map arithmetic

Theorem raw_log_fixed_tail_post_frame:
  emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
  compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\
  fn_has_code alloc_sa data_sa func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\
  (!name b n. local_region cenv ee.scopes s name b n ==>
    regions_disjoint (w2n w) 32 b n) /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint (w2n w) 32 b n) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  u = ((mstore (w2n w) word s) with
    <|vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
      vs_inst_idx := LENGTH sb.cs_current_insts|>) ==>
  expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
  expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
  (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
  stmt_state_rel H ctx func cenv cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) u /\
  storage_well_formed_on cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H) /\
   wb_frame cenv es ee sa s0 s` by (fs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee (mstore (w2n w) word s)` by
    (irule literal_mstore_state_rel >>
     reverse conj_tac >- simp[] >>
     qexistsl [`w2n w`, `mk_inst alloc_sa.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString alloc_sa.cs_next_var)]`, `32`] >>
     simp[mk_inst_def] >> conj_tac
     >- (rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
     drule_all actual_alloc_buffer_site >> simp[mk_inst_def, dimword_def]) >>
  `!name b n. local_region cenv es.scopes s0 name b n ==>
     regions_disjoint (w2n w) 32 b n` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b n` by
       (irule local_region_frame_fwd >>
        qexistsl [`s0`, `sa`, `es.scopes`] >> fs[wb_frame_def, locals_kept_def]) >>
     metis_tac[]) >>
  `wb_frame cenv es ee sa s0 (mstore (w2n w) word s)` by
    (`!off sz. (w2n w + 32 <= off \/ off + sz <= w2n w) ==>
        mem_bytes_at off sz (mstore (w2n w) word s).vs_memory =
        mem_bytes_at off sz s.vs_memory` by metis_tac[mstore_mem_bytes_at_disjoint] >>
     qpat_x_assum `!off sz. _` (assume_tac o SRULE [mstore_def]) >>
     fs[wb_frame_def] >> simp[mstore_def, lookup_var_def] >>
     conj_tac
     >- (rpt strip_tac >> irule EQ_TRANS >>
         qexists `mem_bytes_at off sz s.vs_memory` >> conj_tac
         >- (first_x_assum irule >>
             qpat_x_assum `!aid b n. _ ==> regions_disjoint _ _ b n`
               (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
             simp[regions_disjoint_def]) >> metis_tac[]) >>
     irule locals_kept_regions_tail >> qexists `s` >> simp[] >>
     rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "bound" >>
  conj_tac >- suspend "history" >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- suspend "value" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "state" >>
  suspend "storage"
QED
Resume raw_log_fixed_tail_post_frame[post]:
  `stmt_state_rel H ctx func cenv cx
     (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) u` by
    (simp[stmt_state_rel_inst_idx] >> drule raw_log_state_rel >> simp[mstore_def]) >>
  `storage_well_formed_on cx
     (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H)` by
    (fs[storage_well_formed_on_def] >> rpt strip_tac >>
     Cases_on `b` >> fs[get_storage_def] >> metis_tac[get_storage_def]) >>
  `wb_frame cenv es (ee with logs := ee.logs ++
     [encode_raw_event_values cx.txn.target vals bs]) sa s0 u` by
    (qpat_x_assum `wb_frame _ _ _ _ _ (mstore _ _ _)` mp_tac >>
     simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def, mstore_def] >>
     strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  fs[expr_post_def, wb_frame_def] >>
  simp[expr_val_rel_def, expr_val_at_def, is_word_type_def,
       eval_operand_def, valueEncodingDefsTheory.val_in_memory_def,
       val_footprint_def, valueEncodingTheory.type_memory_size_def,
       valueEncodingDefsTheory.val_wf_def] >> first_assum MATCH_ACCEPT_TAC
QED
Resume raw_log_fixed_tail_post_frame[bound]:
  simp[exprSimMemDefsTheory.expr_store_bound_def, exprSimPropsTheory.val_store_size_def,
       valueEncodingTheory.type_memory_size_def]
QED
Resume raw_log_fixed_tail_post_frame[history]:
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  pure_rewrite_tac[emit_void_def, GSYM emit_inst_def] >> strip_tac >>
  qpat_assum `emit_inst MSTORE _ _ _ = _`
    (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >> strip_tac >>
  qpat_assum `emit_inst LOG _ _ _ = _`
    (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >> strip_tac >>
  fs[alloca_history_def, mstore_def, fragExecTheory.fn_has_code_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH sm.cs_current_insts`
  >- metis_tac[] >>
  qpat_x_assum `_ ++ _ ++ _ <<= _` mp_tac >>
  rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN] >>
  `k = LENGTH sm.cs_current_insts \/ k = LENGTH sm.cs_current_insts + 1` by decide_tac >>
  gvs[EL_APPEND_EQN, mk_inst_def]
QED
Resume raw_log_fixed_tail_post_frame[value]:
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptrDisciplineTheory.op_taint_def,
       valueEncodingDefsTheory.val_in_memory_def, val_footprint_def,
       valueEncodingTheory.type_memory_size_def]
QED
Resume raw_log_fixed_tail_post_frame[buffer]:
  simp[is_word_type_def, ptr_buf_ok_def,
       exprLoweringTheory.lowered_value_type_def, compileEnvTheory.type_memory_bytes_def]
QED
Resume raw_log_fixed_tail_post_frame[state]:
  simp[stmt_state_rel_inst_idx] >> drule raw_log_state_rel >> simp[mstore_def]
QED
Resume raw_log_fixed_tail_post_frame[storage]:
  fs[storage_well_formed_on_def] >> rpt strip_tac >>
  Cases_on `b` >> fs[get_storage_def] >> metis_tac[get_storage_def]
QED
Finalise raw_log_fixed_tail_post_frame
