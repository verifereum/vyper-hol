(* Exposed run endpoints for the RawLog memory continuations. *)
Theory bodyMemRawLogExecution
Ancestors
  rawLogCoreFrame
  bodyMemRawLogSuffix bodySimRawLog exprSimRawLog exprSimHash
  compileEnv emitHelper exprLoweringProps emitHelperProps fragExec
  venomInst venomState venomExecSemantics words list rich_list
  loweringPosts vyperEvent bodyMemBiSha256Compose
  stmtForArrayMemoryBodyEntry entrySinkExtraction exprSimAlloc
  stmtSimDefs exprSimSend

Theorem raw_log_dynamic_suffix_shape[local]:
  emit_op MLOAD [x] sm = (len,s1) /\
  emit_op ADD [x; Lit 32w] s1 = (payload_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;payload_op]) [] s2 = (u,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb = emitted_insts sm s2 ++
    [mk_inst s2.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;payload_op]) []] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem raw_log_dynamic_suffix_run[local]:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = (u,sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\ LENGTH ops <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++ REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 es sa s0 s /\ sa.cs_next_var <= sm.cs_next_var ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel H ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t /\
    wb_frame cenv es0
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t
Proof
  strip_tac >> drule_all raw_log_dynamic_prepare_frame >> strip_tac >>
  `?t'. step_inst_base (mk_inst s2.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) t = OK t' /\
    stmt_state_rel H ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t' /\
    wb_frame cenv es0
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t'` by
    (irule raw_log_core_frame >> simp[mk_inst_def] >>
     qexistsl_tac [`ops`, `len_op`, `ptr_op`,
                  `n2w (b + 32)`, `n2w (LENGTH bs)`] >> simp[dimword_def]) >>
  drule_all raw_log_dynamic_suffix_shape >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  fs[run_inst_seq_def]
QED

Theorem raw_log_dynamic_tail_mem_counted:
  expr_has_effect e /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = (u,sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\ LENGTH ops <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++ REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     storage_well_formed_on cx es (FST H)) /\
  valid_horizon cx st0 H0 es.storage_trace /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 es sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  b + 32 <= s.vs_alloca_next /\
  (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       expr_post H ctx func cenv cx e es0 sa sb s0
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
         NoneV (Lit 0w) t) /\ alloca_history func t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     ?t'. run_inst_seq (emitted_insts sm sb) s = OK t' /\
       stmt_state_rel H ctx func cenv cx
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t' /\
       wb_frame cenv es0
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
         sa s0 t'` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx es s` by metis_tac[] >>
     drule_all raw_log_dynamic_suffix_run >> strip_tac >>
     qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> ?t'. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule_all raw_log_dynamic_suffix_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule raw_log_dynamic_suffix_mem_ok >>
     qexistsl_tac [`b`, `len_op`, `LENGTH (bs:word8 list)`, `ops`, `ptr_op`,
                   `s1`, `s2`, `u`, `data_op`] >> simp[]) >>
  `alloca_inv s` by
    (`stmt_state_rel H0 ctx func cenv cx es s` by metis_tac[] >>
     fs[stmt_state_rel_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
       by decide_tac >> simp[DROP_APPEND]) >>
  drule_all array_prefix_counted_history >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all sha256_run_inst_seq_alloca_next_mono >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts`
    by (qpat_x_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `!n. wb_frame cenv es0 (es with logs := es.logs ++
     [encode_raw_event_values cx.txn.target vals bs]) sa s0
     (t with vs_inst_idx := n)` by
    (gen_tac >>
     qpat_x_assum `wb_frame cenv es0 (es with logs := _) sa s0 t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
     disch_then strip_assume_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- metis_tac[LENGTH] >>
  reverse conj_tac >-
    (qpat_x_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> ?t'. _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `t2 = t` by
    (qpat_x_assum `run_inst_seq _ s = OK t2` mp_tac >>
     qpat_x_assum `run_inst_seq _ s = OK t` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `storage_well_formed_on cx (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H)` by
    (`(es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]).accounts = es.accounts /\
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]).tStorage = es.tStorage` by simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx]
QED

Theorem raw_log_fixed_suffix_shape[local]:
  emit_void MSTORE [ptr_op; data_op] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [] s1 = (u',sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb = emitted_insts sm s1 ++
    [mk_inst s1.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) []] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []
Proof
  simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem raw_log_mstore_operands[local]:
  eval_operands ops (mstore p w s) = eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def, eval_operand_mstore]
QED

Theorem raw_log_fixed_suffix_run[local]:
  emit_void MSTORE [ptr_op; data_op] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [] s1 = (u',sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sa s0 s /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel H ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t /\
    wb_frame cenv es0
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t
Proof
  strip_tac >> drule_all raw_log_fixed_store_frame >> strip_tac >>
  `?t. step_inst_base (mk_inst s1.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [])
      (mstore (w2n p) w s) = OK t /\
    stmt_state_rel H ctx func cenv cx
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t /\
    wb_frame cenv es0
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) sa s0 t` by
    (irule raw_log_core_frame >> simp[mk_inst_def] >>
     qexists_tac `32w` >>
     simp[eval_operand_def, eval_operand_mstore, raw_log_mstore_operands, dimword_def]) >>
  drule_all raw_log_fixed_suffix_shape >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  fs[run_inst_seq_def]
QED

Theorem raw_log_fixed_tail_mem_counted:
  expr_has_effect e /\
  emit_void MSTORE [ptr_op; data_op] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) [] s1 = (u',sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     storage_well_formed_on cx es (FST H)) /\
  valid_horizon cx st0 H0 es.storage_trace /\ wb_frame cenv es0 es sa s0 s /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  w2n p + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       expr_post H ctx func cenv cx e es0 sa sb s0
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
         NoneV (Lit 0w) t) /\ alloca_history func t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     ?t'. run_inst_seq (emitted_insts sm sb) s = OK t' /\
       stmt_state_rel H ctx func cenv cx
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) t' /\
       wb_frame cenv es0
         (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs])
         sa s0 t'` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx es s` by metis_tac[] >>
     drule_all raw_log_fixed_suffix_run >> strip_tac >>
     qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> ?t'. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule_all raw_log_fixed_suffix_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule raw_log_fixed_suffix_mem_ok >>
     qexistsl_tac [`ops`, `p`, `ptr_op`, `s1`, `u`, `u'`, `w`, `data_op`] >> simp[]) >>
  `alloca_inv s` by
    (`stmt_state_rel H0 ctx func cenv cx es s` by metis_tac[] >>
     fs[stmt_state_rel_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
       by decide_tac >> simp[DROP_APPEND]) >>
  drule_all array_prefix_counted_history >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all sha256_run_inst_seq_alloca_next_mono >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts`
    by (qpat_x_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `!n. wb_frame cenv es0 (es with logs := es.logs ++
     [encode_raw_event_values cx.txn.target vals bs]) sa s0
     (t with vs_inst_idx := n)` by
    (gen_tac >>
     qpat_x_assum `wb_frame cenv es0 (es with logs := _) sa s0 t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
     disch_then strip_assume_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- metis_tac[LENGTH] >>
  reverse conj_tac >-
    (qpat_x_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> ?t'. _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `t2 = t` by
    (qpat_x_assum `run_inst_seq _ s = OK t2` mp_tac >>
     qpat_x_assum `run_inst_seq _ s = OK t` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `storage_well_formed_on cx (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H)` by
    (`(es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]).accounts = es.accounts /\
      (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bs]).tStorage = es.tStorage` by simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx]
QED
