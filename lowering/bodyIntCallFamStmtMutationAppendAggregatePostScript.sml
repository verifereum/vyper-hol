(* Source and header landing for aggregate storage Append. *)
Theory bodyIntCallFamStmtMutationAppendAggregatePost
Ancestors
  stmtSimAppendStorage vyperStorageBackend vyperState vyperStorage
  valueEncoding valueEncodingProofs words integer_word accountsRelProps
  placeStore stmtSimAppendStorageCompose appendStorageRel appendStorageStageRuns
  fragGasPath exprSimHashBoundary loweringStateRelDefs vyperValue vfmState
  compileEnv exprLoweringProps emitHelper emitHelperProps venomState venomInst
  stateFrame stmtReasonLitFragMemory

Theorem intcall_append_aggregate_success:
  ~cx.txn.is_static /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  len < cap /\ encode_value tv v = SOME writes ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (INL (),
   set_storage cx
     (set_storage cx es tr
       (apply_writes (slot + n2w (1 + len * type_slot_size tv)) writes
         (get_storage cx es tr))) tr
     (update_storage slot (n2w (len+1))
       (apply_writes (slot + n2w (1 + len * type_slot_size tv)) writes
         (get_storage cx es tr))))
Proof
  strip_tac >> gvs[] >>
  simp[append_storage_writes,ignore_bind_def,bind_def,
       write_storage_slot_eq,get_storage_after_set,apply_writes_def,
       encode_value_def,encode_base_to_slot_def,integer_wordTheory.i2w_def]
QED

Theorem intcall_append_header_dead_bytes[local]:
  w2n (slot:bytes32) + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) ==>
  !st u j b.
    dead_bytes (update_storage slot u st) (w2n slot) (ArrayTV tv (Dynamic cap)) j b <=>
    dead_bytes st (w2n slot) (ArrayTV tv (Dynamic cap)) j b
Proof
  strip_tac >> rpt gen_tac >> simp[dead_bytes_def] >>
  `!i. i < cap ==>
    (dead_bytes (update_storage slot u st) (w2n slot + (i * type_slot_size tv + 1)) tv j b <=>
     dead_bytes st (w2n slot + (i * type_slot_size tv + 1)) tv j b)` suffices_by metis_tac[] >>
  rpt strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `(i+1)*type_slot_size tv <= cap*type_slot_size tv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `i' < dimword (:256) /\ i' <> w2n slot` by
    (qpat_x_assum `(i+1)*_ <= _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,arithmeticTheory.MULT_CLAUSES] >>
     fs[type_slot_size_def] >> decide_tac) >>
  `(n2w i':bytes32) <> slot` by
    (strip_tac >> `w2n (n2w i':bytes32) = w2n slot` by simp[] >>
     gvs[wordsTheory.w2n_n2w]) >>
  simp[lookup_storage_def,update_storage_def,combinTheory.APPLY_UPDATE_THM]
QED

Theorem intcall_append_header_state[local]:
  stmt_state_rel ctx func ce cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  stmt_state_rel ctx func ce cx
    (set_storage cx es tr (update_storage slot u (get_storage cx es tr)))
    (if tr then tstore slot u s else sstore slot u s)
Proof
  strip_tac >> irule place_store_backend_state >>
  qexistsl [`es`,`get_storage cx es tr`] >>
  simp[get_storage_def,GSYM get_storage_backend_eq,set_storage_backend_eq] >>
 (`storage_dead cx tr (update_storage slot u (get_storage cx es tr)) =
       storage_dead cx tr (get_storage cx es tr)` by
        (irule storage_dead_update_in_region >>
         goal_assum (drule_at Any) >> strip_tac >>
         simp[type_slot_size_def] >> irule intcall_append_header_dead_bytes >> simp[]) >>
      simp[]) >>
  Cases_on `tr` >> simp[get_storage_def,lookup_account_def]
QED

Theorem intcall_append_aggregate_header_landing:
  emit_op ADD [lop;Lit 1w] sa = (nop,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sm = ((),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  fresh_vars_wrt sa s /\ eval_operand lop s = SOME len /\
  eval_operand bop s = SOME slot /\ stmt_state_rel ctx func ce cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx
      (set_storage cx es tr (update_storage slot (len+1w) (get_storage cx es tr))) t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Lit 1w) s = SOME 1w` by simp[eval_operand_def] >>
  drule_all emitHelperPropsTheory.emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `state_frame u = state_frame s` by
    (irule append_storage_seq_frame >> qexists `emitted_insts sa sm` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `~u.vs_call_ctx.cc_static /\ eval_operand bop u = SOME slot` by
    (fs[state_frame_def] >> metis_tac[]) >>
  drule_all append_storage_store_run >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (metis_tac[stmt_state_rel_operand_frame]) >>
  drule_all intcall_append_header_state >>
  disch_then (qspec_then `len+1w` assume_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (if tr then tstore slot (len+1w) u else sstore slot (len+1w) u)` by
    (irule run_inst_seq_compose_ok >> qexistsl [`u`,`sm`] >> simp[]) >>
  `same_blocks sa sb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     metis_tac[same_blocks_trans]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[emit_op_def,emit_void_def,fresh_id_def,fresh_var_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp[rich_listTheory.DROP_APPEND2,mk_inst_def,is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all hash_run_path >> strip_tac >>
  qexists `(if tr then tstore slot (len+1w) u else sstore slot (len+1w) u)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_inst_idx,state_frame_def,same_blocks_def,sstore_def,tstore_def,eval_operand_def]
QED
