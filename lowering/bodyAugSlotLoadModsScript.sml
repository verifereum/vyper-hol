(* Read the old AugAssign word from the selected linked storage backend. *)
Theory bodyAugSlotLoadMods
Ancestors
  bodyWriteTargetStageMods augAssignFullLoadStorageStep
  stmtSimAugAssignPlaceStorage exprPtrUnwrapCopyEdges accountsRelProps
  bodyFullShadowBodyInv bodyPtrDefs exprSimUnwrap sourceUnitExecution
  exprLoweringProps bodyPtrBopInLiveStorage
  loweringPosts loweringStateRelDefs codegenRel emitHelper loweringShapeRules freshWrites
  vyperStorageFootprint vyperStorageBackend vyperState
  ptrDiscipline venomInst venomState vfmState compileEnv pred_set words arithmetic

Theorem aug_slot_word_matches_mods[local]:
  stmt_state_rel H ctx func cenv cx st s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  storage_read_live H tr (get_storage cx st tr) slot tv ==>
  (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur
Proof
  strip_tac >>
  `storage_agree (storage_dead H tr (get_storage cx st tr))
      (get_storage cx st tr) (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
         lookup_account_def, get_storage_def]) >>
  `w2n slot + type_slot_size tv <= dimword (:256)` by
    (drule_all word_type_slot_size >> strip_tac >>
     qspec_then `slot` mp_tac w2n_lt >> simp[]) >>
  drule_all_then assume_tac storage_range_agree_of_live >>
  `read_storage_slot cx tr slot tv st = (INL cur,st)` by fs[read_place_def] >>
  drule_all_then assume_tac aug_place_storage_read_holds >>
  irule storage_holds_load >> goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_slot_word_untainted_mods[local]:
  storage_place_observed H (StoragePlace tr slot tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn s ==>
  !b. (slot,b) NOTIN (if tr then tn.t_trans else tn.t_stor)
Proof
  strip_tac >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  `!raw b. ~storage_dead H tr raw (w2n slot) b` by
    (rpt gen_tac >>
     `storage_read_live H tr raw slot tv` by
       (irule storage_place_observed_read_live >> simp[]) >>
     `!bs j b. ~dead_bytes raw bs tv j b` by metis_tac[evaluated_word_deadless] >>
     fs[storage_read_live_def] >>
     qpat_assum `!j b. storage_dead _ _ _ _ _ ==> _`
       (qspecl_then [`w2n slot`,`b`] mp_tac) >> simp[]) >>
  fs[dead_lo_ok_mods_def, stor_taint_ok_at_def, cx_dead_def, SUBSET_DEF] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >> gvs[] >>
  Cases_on `tr` >> gvs[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem aug_slot_load_resources_mods[local]:
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
  valid_horizon cx st0 H st.storage_trace /\ is_word_type ty /\
  dead_lo_ok_mods H D lo cenv cx /\
  write_target_post_mods H D lo d ctx func cenv cx bt
    es sa sb s0 st (PlaceR (StoragePlace tr slot tv)) (Type ty) r G0 tn0 G tn s ==>
  FST (SND r) = SOME (slot_loc tr) /\ eval_operand (FST r) s = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ op_taint tn (FST r) = {} /\
  (!q. FST r = Var q ==> not_fresh_at sb q) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!b. (slot,b) NOTIN (if tr then tn.t_trans else tn.t_stor)) /\
  (!iid out. ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst iid (if tr then TLOAD else SLOAD) [FST r] [out]) s) /\
  ?cur. read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
    place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
    value_has_type tv cur /\
    (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur
Proof
  strip_tac >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_all_then strip_assume_tac aug_place_target_storage_ready >>
  drule_all_then strip_assume_tac aug_place_storage_read_ready >>
  drule_all_then assume_tac aug_slot_word_matches_mods >>
  drule_all_then assume_tac aug_place_target_observed >>
  `stor_taint_ok_at D tn s /\ allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_all_then assume_tac aug_slot_word_untainted_mods >>
  simp[] >> rpt gen_tac >> irule ptr_inst_ok_slot_load >>
  Cases_on `tr` >> simp[]
QED

Theorem augassign_slot_load_mods:
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
  is_word_type ty /\ storage_trace_domain cx st0 st.storage_trace /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx /\
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt
      es sa sb s0 st (PlaceR (StoragePlace tr slot tv)) (Type ty) r G0 tn0 G tn s) /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sb = (old,sc) /\ fn_has_code sb sc func ==>
  ?cur u G1 tn1.
    FST (SND r) = SOME (slot_loc tr) /\ eval_operand (FST r) s = SOME slot /\
    read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
    place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    (!H. valid_horizon cx st0 H st.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1)) /\
    eval_operand old u = SOME (typed_val_to_w256 tv cur) /\
    eval_operand (FST r) u = SOME slot /\
    op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
    (!q. old = Var q ==> not_fresh_at sc q) /\
    (!q. FST r = Var q ==> not_fresh_at sc q) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
      FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac aug_slot_load_resources_mods >>
  drule_then strip_assume_tac emit_op_facts >>
  `!q. FST r = Var q ==> not_fresh_at sc q` by
    metis_tac[not_fresh_at_mono, LESS_EQ_ADD] >>
  qabbrev_tac `x = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `opc = if tr then TLOAD else SLOAD` >>
  qabbrev_tac `i = mk_inst sb.cs_next_id opc [FST r] [x]` >>
  qabbrev_tac `raw = update_var x (if tr then tload slot s else sload slot s) s` >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac aug_slot_load_resources_mods >>
     simp[Abbr `i`, Abbr `opc`]) >>
  qexistsl_tac [`cur`,`raw with vs_inst_idx := SUC s.vs_inst_idx`,
                `step_prov PG G i raw`,`step_taint i s raw tn`] >>
  simp[] >>
  qpat_assum `(if tr then tload slot s else sload slot s) = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  mp_tac (BETA_RULE (Q.ISPEC `\H. valid_horizon cx st0 H st.storage_trace`
    augassign_storage_load_joint_step)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = {}`)) >>
  disch_then (qspecl_then [`DF`,`lo`,`explicit`,`ctx`,`PG`] mp_tac) >>
  simp[Abbr `x`, Abbr `i`, Abbr `opc`, Abbr `raw`] >>
  disch_then (qspecl_then [`G`,`tr`] mp_tac) >> simp[]
QED
