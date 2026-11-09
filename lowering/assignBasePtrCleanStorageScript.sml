(* Clean scalar storage writes use deadness transport, not just taint subsets. *)
Theory assignBasePtrCleanStorage
Ancestors assignBasePtrWordStore accountsRelProps bodyPtrDefs ptrDiscipline
  venomState venomExecSemantics venomInst vyperStorage vyperValue
  finite_map pred_set words vfmState codegenRel fragGasPathPtr
  appendStorageGhostPtr

Theorem assign_base_clean_key_update_subset:
  !X k Y. X SUBSET Y ==> key_update X k {} SUBSET Y
Proof
  simp[key_update_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem assign_base_clean_storage_taint:
  !cx tn tf s tr k w.
    stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans = key_update tn.t_trans k {} /\ tf.t_stor = tn.t_stor
     else tf.t_stor = key_update tn.t_stor k {} /\ tf.t_trans = tn.t_trans) /\
    storage_dead cx tr
      (update_storage k w (if tr then contract_transient s else contract_storage s)) =
      storage_dead cx tr (if tr then contract_transient s else contract_storage s) ==>
    stor_taint_ok cx tf (if tr then tstore k w s else sstore k w s)
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[stor_taint_ok_def, cx_dead_def, tstore_def, sstore_def,
       contract_transient_def, contract_storage_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  irule assign_base_clean_key_update_subset >> simp[lookup_account_def]
QED

Theorem assign_base_clean_storage_word_taint:
  !cx tn tf s tr k w mid name subs tv.
    stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans = key_update tn.t_trans k {} /\ tf.t_stor = tn.t_stor
     else tf.t_stor = key_update tn.t_stor k {} /\ tf.t_trans = tn.t_trans) /\
    declared_storage_region cx mid name subs = SOME (tr,k,tv) /\
    type_slot_size tv = 1 ==>
    stor_taint_ok cx tf (if tr then tstore k w s else sstore k w s)
Proof
  rpt gen_tac >> strip_tac >> irule assign_base_clean_storage_taint >>
  simp[] >> conj_tac >- (irule storage_dead_update_word_region >> metis_tac[]) >>
  qexists_tac `tn` >> simp[]
QED

Theorem assign_base_clean_storage_field_taint:
  !cx tn tf s tr k w mid name fs fld off ftv.
    stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    tf.t_imm = tn.t_imm /\
    (if tr then
       tf.t_trans = key_update tn.t_trans (k+n2w off) {} /\ tf.t_stor = tn.t_stor
     else tf.t_stor = key_update tn.t_stor (k+n2w off) {} /\ tf.t_trans = tn.t_trans) /\
    declared_storage_region cx mid name [] = SOME (tr,k,StructTV fs) /\
    struct_field_slot fs fld = SOME (off,ftv) /\ type_slot_size ftv = 1 ==>
    stor_taint_ok cx tf
      (if tr then tstore (k+n2w off) w s else sstore (k+n2w off) w s)
Proof
  rpt gen_tac >> strip_tac >> irule assign_base_clean_storage_taint >>
  simp[] >> conj_tac >- (irule storage_dead_update_struct_word_field >> metis_tac[]) >>
  qexists_tac `tn` >> simp[]
QED

Theorem assign_base_clean_storage_step_frame:
  !PG G tn s u id tr addr value k.
    eval_operand addr s = SOME k /\ op_taint tn value = {} /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
    step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) u = G /\
    (step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s u tn).t_var = tn.t_var /\
    (step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s u tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s u tn).t_imm = tn.t_imm /\
    (if tr then
       (step_taint (mk_inst id TSTORE [addr; value] []) s u tn).t_trans =
         key_update tn.t_trans k {} /\
       (step_taint (mk_inst id TSTORE [addr; value] []) s u tn).t_stor = tn.t_stor
     else
       (step_taint (mk_inst id SSTORE [addr; value] []) s u tn).t_stor =
         key_update tn.t_stor k {} /\
       (step_taint (mk_inst id SSTORE [addr; value] []) s u tn).t_trans = tn.t_trans)
Proof
  rpt gen_tac >> Cases_on `tr` >> strip_tac >>
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
       set_var_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, DRESTRICT_UNIV, new_site_bytes_def, FLOOKUP_DEF,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, EXTENSION] >> metis_tac[]
QED

Theorem assign_base_clean_storage_counted:
  !s fn bb id tr addr value tn G ctx D PG k w u Gf tf.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] []) /\
    op_taint tn addr = {} /\ op_taint tn value = {} /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
    eval_operand addr s = SOME k /\
    eval_operand value s = SOME w /\
    u = ((if tr then tstore k w s else sstore k w s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) (if tr then tstore k w s else sstore k w s) /\
    tf = step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s (if tr then tstore k w s else sstore k w s) tn ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id (if tr then TSTORE else SSTORE)
     [addr; value] []) s =
     OK (if tr then tstore k w s else sstore k w s)` by
    (Cases_on `tr` >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]) >>
  gvs[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] [])
      (if tr then tstore k w s else sstore k w s)`,
    `(if tr then tstore k w s else sstore k w s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst id (if tr then TSTORE else SSTORE) [addr; value] []) s
      (if tr then tstore k w s else sstore k w s) tn`] >> conj_tac
  >- (Cases_on `tr` >> simp[cj 1 gas_path_ptr_rules, sstore_def, tstore_def]) >>
  irule assign_base_storage_word_edge_ptr >>
  simp[] >> Cases_on `tr` >> simp[]
QED

Theorem assign_base_clean_storage_ghost:
  !d cenv cx es es' G tn s PG id tr addr value k w sa u Gf tf.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    es'.scopes = es.scopes /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    eval_operand addr s = SOME k /\ op_taint tn value = {} /\
    storage_dead cx tr
      (update_storage k w (if tr then contract_transient s else contract_storage s)) =
      storage_dead cx tr (if tr then contract_transient s else contract_storage s) /\
    u = ((if tr then tstore k w s else sstore k w s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) (if tr then tstore k w s else sstore k w s) /\
    tf = step_taint (mk_inst id (if tr then TSTORE else SSTORE)
      [addr; value] []) s (if tr then tstore k w s else sstore k w s) tn ==>
    ghost_inv d cenv cx es' Gf tf u /\ ghost_kept cenv es sa G tn s Gf tf
Proof
  rpt gen_tac >> strip_tac >>
  `(if tr then tstore k w s else sstore k w s).vs_allocas = s.vs_allocas /\
       (if tr then tstore k w s else sstore k w s).vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  drule_all assign_base_clean_storage_step_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`, `tr`] assume_tac) >>
  `stor_taint_ok cx tf (if tr then tstore k w s else sstore k w s)` by
    (irule assign_base_clean_storage_taint >>
     simp[] >> qexists_tac `tn` >> Cases_on `tr` >> gvs[ghost_inv_def]) >>
  reverse conj_tac
  >- (irule ghost_kept_old_transport >> Cases_on `tr` >>
      gvs[op_taint_def]) >>
  irule ghost_inv_old_transport >> conj_tac
  >- (Cases_on `tr` >> gvs[stor_taint_ok_def]) >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
  Cases_on `tr` >> gvs[op_taint_def, tstore_def, sstore_def, lookup_var_def,
    stor_taint_ok_def]
QED
