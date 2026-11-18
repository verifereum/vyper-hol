(* Storage resources at the actual joint target endpoint. *)
Theory augAssignFullLoadStorageResources
Ancestors
  stmtSimAugAssignPlaceStorage bodyFullTargetDefs bodyPtrDefs
  bodyPtrBopInLiveStorage exprSimUnwrap accountsRelProps
  sourceUnitExecution ptrSafeRun ptrDiscipline contextCodegenRel codegenRel loweringPosts
  venomExecSemantics venomInstProofs venomInst venomState
  loweringStateRelDefs compileEnv finite_map words pred_set list arithmetic

val load_steps = LIST_CONJ (List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``SLOAD``, ``TLOAD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs));

Theorem augassign_storage_load_resources:
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
  valid_horizon cx st0 H st.storage_trace /\
  target_post H ctx func cenv cx es sa sb s0 st
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r s /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv)) r G tn s /\
  ghost_inv_at D lo d cenv cx st G tn s /\
  dead_lo_ok H D lo cenv cx /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  is_word_type ty
  ==>
  ?cur.
    read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
    place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv cur /\
    eval_operand (FST r) s = SOME slot /\
    op_taint tn (FST r) = {} /\
    op_prov G (FST r) = NONE /\
    (!q. FST r = Var q ==> not_fresh_at sb q) /\
    (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur /\
    (!b. (slot,b) NOTIN (if tr then tn.t_trans else tn.t_stor)) /\
    (!iid out. ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst iid (if tr then TLOAD else SLOAD) [FST r] [out]) s)
Proof
  strip_tac >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [target_post_def] >> strip_tac >>
  gvs[place_ptr_rel_def] >>
  `slots_in_range (get_storage cx st tr) (w2n slot) tv /\
   storage_read_live H tr (get_storage cx st tr) slot tv` by
    metis_tac[aug_place_target_storage_ready] >>
  drule_all aug_place_storage_read_ready >> strip_tac >>
  ` (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur` by
    metis_tac[aug_place_storage_load_ready] >>
  `storage_place_observed H (StoragePlace tr slot tv)` by
    metis_tac[aug_place_target_observed] >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  `!raw b. ~storage_dead H tr raw (w2n slot) b` by suspend "deadless" >>
  `stor_taint_ok_at D tn s /\ allocas_from lo s` by
    fs[ghost_inv_at_def] >>
  `!b. (slot,b) NOTIN (if tr then tn.t_trans else tn.t_stor)` by
    suspend "clean" >>
  qexists_tac `cur` >> fs[target_ptr_ok_def] >>
  suspend "instruction"
QED

Resume augassign_storage_load_resources[deadless]:
  rpt gen_tac >>
  `storage_read_live H tr raw slot tv` by
    (irule storage_place_observed_read_live >> simp[]) >>
  `!bs j b. ~dead_bytes raw bs tv j b` by
    metis_tac[evaluated_word_deadless] >>
  gvs[storage_read_live_def] >>
  qpat_x_assum `!j b. storage_dead _ _ _ _ _ ==> _`
    (qspecl_then [`w2n slot`, `b`] mp_tac) >> simp[]
QED

Resume augassign_storage_load_resources[clean]:
  fs[dead_lo_ok_def, stor_taint_ok_at_def, cx_dead_def, SUBSET_DEF] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >> gvs[] >>
  Cases_on `tr` >> gvs[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Resume augassign_storage_load_resources[instruction]:
  rpt gen_tac >> Cases_on `tr` >>
  simp[ptr_inst_ok_def, mk_inst_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  simp[step_inst_non_invoke, load_steps, mk_inst_def, exec_read1_def,
       update_var_def, AllCaseEqs()]
QED

Finalise augassign_storage_load_resources
