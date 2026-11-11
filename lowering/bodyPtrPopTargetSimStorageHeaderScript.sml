Theory bodyPtrPopTargetSimStorageHeader
Ancestors
  bodyPtrDefs targetPlaceLive accountsRelProps exprLoweringProps
  compileEnv loweringStateRelDefs ptrDiscipline vyperStorageBackend venomState finite_map pred_set
  bodyPtrBopInSlotLoad

Theorem target_storage_header_clean_ptr:
  stmt_state_rel ctx func cenv cx es s /\ stor_taint_ok cx tn s /\
  storage_read_live cx tr (get_storage cx es tr) slot tv /\
  0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
     (get_storage cx es tr) (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
         get_storage_def, vfmStateTheory.lookup_account_def]) >>
  drule storage_agree_storage_dead >> strip_tac >>
  `!b. ~storage_dead cx tr
       (if tr then contract_transient s else contract_storage s) (w2n slot) b` by
    metis_tac[storage_read_live_head] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, key_taint_def, SUBSET_DEF,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, EXTENSION] >>
  gen_tac >> disj2_tac >> strip_tac >>
  first_x_assum drule >> simp[pairTheory.PAIR_EQ] >> metis_tac[]
QED

Theorem target_pure_storage_header_clean_ptr:
  EVERY pure_expr (target_indices bt) /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),ee) /\
  stmt_state_rel ctx func cenv cx ee s /\ stor_taint_ok cx tn s /\
  0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `ee = es` by metis_tac[nested_pop_eval_base_pure_state] >> gvs[] >>
  drule_all nested_pop_eval_base_live >>
  simp[nested_pop_result_live_def, get_storage_backend_eq] >> strip_tac >>
  irule target_storage_header_clean_ptr >> metis_tac[]
QED

Theorem target_storage_header_value:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (get_storage cx es tr) slot tv /\
  0 < type_slot_size tv ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr)
Proof
  strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
     (get_storage cx es tr) (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
         get_storage_def, vfmStateTheory.lookup_account_def]) >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >>
  simp[tload_def, sload_def, vfmStateTheory.lookup_storage_def, contract_storage_def,
       contract_transient_def]
QED

Theorem target_pure_storage_header_path_ptr:
  EVERY pure_expr (target_indices bt) /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),ee) /\
  stmt_state_rel ctx func cenv cx ee s /\ stor_taint_ok cx tn s /\
  0 < type_slot_size tv /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) /\
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} ==>
  ?H. gas_path_ptr D 0 ctx fn PG G tn s 0 H
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (lookup_storage slot (get_storage cx ee tr)) s
       with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP H out = NONE /\
    (!x. x <> out ==> FLOOKUP H x = FLOOKUP G x)
Proof
  strip_tac >>
  `ee = es` by metis_tac[nested_pop_eval_base_pure_state] >> gvs[] >>
  drule_all target_pure_storage_header_clean_ptr >> strip_tac >>
  `storage_read_live cx tr (get_storage cx ee tr) slot tv` by
    (drule_all nested_pop_eval_base_live >>
     simp[nested_pop_result_live_def, get_storage_backend_eq]) >>
  drule_all target_storage_header_value >> strip_tac >>
  drule_all membership_positioned_slot_load_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED
