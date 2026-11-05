(* Clean storage writes transport the permitted dead-byte taint set. *)
Theory assignTuplePtrStorage
Ancestors
  bodyPtrDefs ptrDiscipline venomState venomInst compileEnv
  finite_map pred_set combin codegenRel vfmState assignTuplePtrStoreFrame
  ptrSafeRun venomExecSemantics venomInstProofs contextCodegenRel
  assignTuplePtrPrefix stmtLowering emitHelper assignTuplePtrCopyEndpoint
  stmtSimAssignStorage tupleTargetStoreProps stmtSimProps stmtSimDefs exprLoweringProps

Theorem clean_storage_step_taint_ptr:
  eval_operand dst s = SOME slot /\ op_taint tn value = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
    s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
    s t tn).t_var = tn.t_var /\
  (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
    s t tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
    s t tn).t_stor = (if tr then tn.t_stor else {(k,b) | (k,b) IN tn.t_stor /\ k <> slot}) /\
  (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
    s t tn).t_trans = (if tr then {(k,b) | (k,b) IN tn.t_trans /\ k <> slot} else tn.t_trans)
Proof
  strip_tac >> Cases_on `tr` >>
  simp[step_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       new_site_bytes_def, set_var_taint_def, imm_taint_def, adopt_reset_def,
       store_taint_def, key_update_def, written_taint_def, range_bytes_def,
       DRESTRICT_UNIV] >>
  simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem clean_storage_stor_taint_ok_ptr:
  stor_taint_ok cx tn s /\ eval_operand dst s = SOME slot /\
  op_taint tn value = {} /\
  (!u mem. storage_dead cx tr (update_storage slot u mem) = storage_dead cx tr mem) ==>
  stor_taint_ok cx
    (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] []) s
      (if tr then tstore slot w s else sstore slot w s) tn)
    (if tr then tstore slot w s else sstore slot w s)
Proof
  strip_tac >>
  `(if tr then tstore slot w s else sstore slot w s).vs_allocas = s.vs_allocas /\
   (if tr then tstore slot w s else sstore slot w s).vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  drule_all clean_storage_step_taint_ptr >>
  disch_then (qspecl_then [`tr`, `iid`] strip_assume_tac) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, sstore_def, tstore_def,
      lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

Theorem clean_storage_ghost_inv_ptr:
  ghost_inv d cenv cx es G tn s /\ es'.scopes = es.scopes /\
  eval_operand dst s = SOME slot /\ op_taint tn value = {} /\
  (!u mem. storage_dead cx tr (update_storage slot u mem) = storage_dead cx tr mem) ==>
  ghost_inv d cenv cx es' G
    (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] []) s
      (if tr then tstore slot w s else sstore slot w s) tn)
    (if tr then tstore slot w s else sstore slot w s)
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  drule_all clean_storage_stor_taint_ok_ptr >>
  disch_then (qspecl_then [`w`, `iid`] assume_tac) >>
  `(if tr then tstore slot w s else sstore slot w s).vs_allocas = s.vs_allocas /\
   (if tr then tstore slot w s else sstore slot w s).vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  drule_all clean_storage_step_taint_ptr >>
  disch_then (qspecl_then [`tr`, `iid`] strip_assume_tac) >>
  irule updated_scope_ghost_inv_ptr >>
  conj_tac
  >- (Cases_on `tr` >>
      gvs[ghost_inv_def, ptr_covers_def, op_taint_def, tstore_def, sstore_def,
          lookup_var_def] >> metis_tac[]) >>
  simp[] >> qexistsl [`es`, `s`, `tn`] >>
  Cases_on `tr` >> simp[op_taint_def, tstore_def, sstore_def, lookup_var_def]
QED

Theorem clean_storage_ptr_inst_ok:
  ~ctx_has_dalloca ctx /\ op_taint tn value = {} /\ op_taint tn dst = {} ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] []) s
Proof
  strip_tac >> Cases_on `tr` >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_write2_def, AllCaseEqs(), sstore_def, tstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem emit_storage_zero_path_ptr:
  compile_store_at_loc imm dst value
    (SOME (if tr then LocTransient else LocStorage)) st = ((), st') /\
  fn_has_code st st' func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\ eval_operand dst s = SOME slot /\
  eval_operand value s = SOME w /\ op_taint tn dst = {} /\
  op_taint tn value = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G
    (step_taint (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
       [dst;value] []) s (if tr then tstore slot w s else sstore slot w s) tn)
    (OK ((if tr then tstore slot w s else sstore slot w s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
     [dst;value] []) (if tr then tstore slot w s else sstore slot w s) = G` by
    simp[step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV] >>
  qpat_assum `step_prov _ _ _ _ = _`
    (fn th => CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV (K (SYM th)))))) >>
  irule emit_inst_zero_path_ptr >>
  `~is_terminator (if tr then TSTORE else SSTORE) /\
   (if tr then TSTORE else SSTORE) <> GAS /\
   (if tr then TSTORE else SSTORE) <> INVOKE` by
    (Cases_on `tr` >> simp[is_terminator_def]) >> simp[] >>
  conj_tac
  >- (Cases_on `tr` >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      gvs[mk_inst_def, exec_write2_def]) >>
  conj_tac
  >- (qexists `st'` >> Cases_on `tr` >>
      gvs[compile_store_at_loc_def, emit_void_def, emit_inst_def]) >>
  irule clean_storage_ptr_inst_ok >> simp[]
QED

Theorem storage_word_endpoint_inv_ptr:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  eval_operand dst s = SOME slot /\ op_taint tn value = {} /\
  (!u mem. storage_dead cx tr (update_storage slot u mem) = storage_dead cx tr mem) /\
  write_storage_slot cx tr slot tv v es = (INL (),es') /\
  encode_value tv v = SOME [(0,w)] ==>
  stmt_state_rel ctx func cenv cx es'
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := idx) /\
  ghost_inv d cenv cx es' G
    (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] []) s
      (if tr then tstore slot w s else sstore slot w s) tn)
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := idx)
Proof
  strip_tac >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  drule tuple_target_storage_scope_frame >> strip_tac >>
  conj_tac >- simp[stmt_state_rel_inst_idx] >>
  simp[ghost_inv_inst_idx] >> irule clean_storage_ghost_inv_ptr >>
  simp[] >> qexists `es` >> simp[]
QED


Theorem tuple_storage_store_head_path_ptr:
  compile_store_at_loc cenv.ce_imm_alloca dst op
    (SOME (if tr then LocTransient else LocStorage)) st = ((),st') /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  (!u mem. storage_dead cx tr (update_storage slot u mem) = storage_dead cx tr mem) /\
  write_storage_slot cx tr slot tv v es = (INL (),es') /\
  encode_value tv v = SOME [(0,typed_val_to_w256 tv v)] /\
  fn_has_code st st' func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  op_taint tn op = {} /\ op_taint tn dst = {} /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t tn'. stmt_state_rel ctx func cenv cx es' t /\
    ghost_inv d cenv cx es' G tn' t /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. lookup_var x t = lookup_var x s) /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\
    (!x. op_taint tn' (Var x) = op_taint tn (Var x)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn' (OK t)
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all emit_storage_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G tn1 (OK t)` >>
  qexistsl [`t`, `tn1`] >>
  conj_tac
  >- (simp[Abbr `t`] >> irule (cj 1 storage_word_endpoint_inv_ptr) >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (simp[Abbr `t`, Abbr `tn1`] >>
      irule (cj 2 storage_word_endpoint_inv_ptr) >> simp[] >> metis_tac[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_var = tn.t_var` by
    (unabbrev_all_tac >> conj_tac
     >- (irule (cj 1 clean_storage_step_taint_ptr) >> simp[] >>
         Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
     irule (cj 2 clean_storage_step_taint_ptr) >> simp[] >>
     Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def]) >>
  simp[op_taint_def] >> simp[Abbr `t`] >>
  Cases_on `tr` >> simp[tstore_def, sstore_def, lookup_var_def]
QED
