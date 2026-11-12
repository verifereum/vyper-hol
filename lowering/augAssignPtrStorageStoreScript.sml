(* Counted clean storage-word writes, shared by roots and struct fields. *)
Theory augAssignPtrStorageStore
Ancestors
  augAssignPtrStore stmtAppendStorageRunPtr appendStorageGhostPtr
  fragGasSeqPtr fragGasPathPtr emitHelperProps emitHelper fragExec
  ptrDiscipline ptrSafeRun bodyPtrDefs rich_list compileEnv venomInst
  accountsRelProps venomState vyperStorage pred_set

Theorem emit_storage_store_path_ptr:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  op_taint tn a = {} /\ op_taint tn v = {} /\
  eval_operand a s = SOME slot /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule_all emit_storage_store_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] assume_tac) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [a;v] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND1] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  drule_all run_inst_seq_gas_path_ptr >>
  Cases_on `tr` >> simp[mk_inst_def]
QED

(* Word-region and struct-field source lemmas supply this dead-map equality.
   It is essential: taint shrinking alone does not preserve a changing bank. *)
Theorem clean_storage_store_taint_ok:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  (!k b. storage_dead cx tr
    (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
    storage_dead cx tr (if tr then contract_transient s else contract_storage s) k b) ==>
  stor_taint_ok cx
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    (if tr then tstore slot w s else sstore slot w s)
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
      key_update_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ghost_inv_storage_word_store:
  ghost_inv d cenv cx es G tn s /\ es'.scopes = es.scopes /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  (!k b. storage_dead cx tr
    (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
    storage_dead cx tr (if tr then contract_transient s else contract_storage s) k b) ==>
  ghost_inv d cenv cx es' G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by fs[ghost_inv_def] >>
  drule_all clean_storage_store_taint_ok >> strip_tac >>
  Cases_on `tr` >>
  gvs[ghost_inv_def, ptr_covers_def, op_taint_def, sstore_def, tstore_def,
      lookup_var_def, stor_taint_ok_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >>
  gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def, sstore_def,
      tstore_def, lookup_var_def]
QED

Theorem ghost_kept_storage_word_store:
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ghost_kept cenv es sa G0 tn0 s0 G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  Cases_on `tr` >> simp[ghost_kept_def, op_taint_def] >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED
