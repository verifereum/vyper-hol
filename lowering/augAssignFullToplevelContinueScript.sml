(* Scalar top-level AugAssign: the observed root protects the final word store. *)
Theory augAssignFullToplevelContinue
Ancestors
  augAssignFullStore augAssignFullStoreGhost stmtSimAssignStorage
  bodySimFull accountsRelProps exprLoweringProps
  vyperStorageFootprint vyperStorageBackend vyperState vyperValue
  venomState bodyPtrDefs ptrDiscipline list
  stmtSimAugAssignStorage exprSimHypsDefs exprSimUnwrap
  vyperTypeStatePreservation vyperTyping vyperInterpreter vyperTypeSystem
  exprSimSource exprSimHyps exprBopSimProps stmtSimAugAssign

Theorem augassign_toplevel_store_relations_full:
  root_es.storage_trace = es.storage_trace ++ [StorageRoot tr slot tvt] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn operated) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  type_slot_size tvt = 1 /\ well_formed_type_value tvt /\
  value_has_type tvt result /\ encode_value tvt result = SOME [(0,w)] /\
  write_storage_slot cx tr (n2w slot) tvt result (mid with gas_obs := []) =
    (INL (),fin) /\
  fin.storage_trace = mid.storage_trace /\ fin.scopes = mid.scopes /\
  operated.vs_call_ctx.cc_address = cx.txn.target ==>
  !H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin
      ((if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)
        with vs_inst_idx := pc) /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin G
      (if tr then tn with t_trans := key_update tn.t_trans (n2w slot) {}
       else tn with t_stor := key_update tn.t_stor (n2w slot) {})
      ((if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)
        with vs_inst_idx := pc)
Proof
  strip_tac >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H root_es.storage_trace` by metis_tac[] >>
  `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    gvs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def] >>
  `stmt_state_rel H ctx func cenv cx mid operated /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn operated` by metis_tac[] >>
  `!u st. storage_dead H tr (update_storage (n2w slot) u st) = storage_dead H tr st`
    by metis_tac[storage_dead_update_word_region] >>
  `stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) operated` by
    simp[stmt_state_rel_start_gas_obs] >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists_tac `mid` >> simp[]) >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  `storage_well_formed_on cx fin (FST H)` by
    metis_tac[typed_write_preserves_storage_well_formed_on] >>
  simp[stmt_state_rel_inst_idx] >>
  irule (INST_TYPE [alpha |-> ``:256``] ghost_inv_at_storage_word_store) >>
  simp[] >> conj_tac
  >- (qexists_tac `H` >> simp[]) >>
  qexists_tac `mid` >> simp[]
QED

Theorem augassign_toplevel_rhs_numeric_facts_full:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  expr_body_pre cenv cx env e root_es /\
  bind (eval_expr cx e) (read_result cx) (root_es with gas_obs := gs) =
    (INL rhs,mid with gas_obs := []) /\
  gas_admissible (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (stmt_res_ok lctx) es /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) ==>
  word_value rhs /\
  (?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    value_has_type etv rhs) /\
  (!n. expr_int_literal e = SOME n ==> rhs = IntV n) /\
  (bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n) /\
  (bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i) /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs (mid with gas_obs := []))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (root_es with gas_obs := gs)` by simp[] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >>
  `word_value rhs /\ ?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    value_has_type etv rhs` by metis_tac[] >>
  qpat_assum `bind (eval_expr cx e) _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL)) >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >> qpat_x_assum `bop = Exp ==> nonneg_int_literal e` mp_tac >>
     simp[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> simp[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i)` by
    (strip_tac >> `shift_amount_ok e` by metis_tac[] >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  simp[] >> reverse conj_tac
  >- (gvs[] >> drule_all augassign_toplevel_binop_admissible >> simp[]) >>
  metis_tac[]
QED
