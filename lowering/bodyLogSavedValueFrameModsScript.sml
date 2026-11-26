Theory bodyLogSavedValueFrameMods
Ancestors
  bodyFullPostsMods targetPurePostTransport bodyPtrIfExpAllocSource
  stateRelProj stateRelProjStorage exprSimSubscriptArrayFrame
  loweringPosts loweringShapeDefs compileEnv venomState context

Theorem log_saved_linked_holds[local]:
  vv_holds_mods ce cx ty raw sv ee s /\ vv_at ce cx ty si ss ee raw sv s /\
  wb_frame ce ee ee ss s u /\
  (!w. eval_operand (vv_operand sv) s = SOME w ==>
       eval_operand (vv_operand sv) u = SOME w) /\
  vv_storage_live H cx sv ee s /\
  storage_rel H cx.txn.target ee u /\ transient_rel H cx.txn.target ee u ==>
  vv_holds_mods ce cx ty raw sv ee u
Proof
  strip_tac >> Cases_on `sv` >> fs[vv_holds_mods_def]
  >- (irule target_saved_holds_frame >> qexistsl [`H`,`s`,`si`,`ss`] >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode` >> fs[]
  >- (gvs[vv_operand_def,immutable_holds_mods_def,immutable_holds_def] >>
      metis_tac[]) >>
  irule target_saved_holds_frame >> qexistsl [`H`,`s`,`si`,`ss`] >> simp[]
QED

Theorem log_saved_value_frame_mods:
  vv_holds_mods ce cx ty raw sv ee s /\ vv_at ce cx ty si ss ee raw sv s /\
  vv_storage_live H cx sv ee s /\
  eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) s /\
  stmt_state_rel H ctx func ce cx ee s /\ stmt_state_rel H ctx func ce cx ee u /\
  wb_frame ce ee ee front s u /\ local_ptrs_reserved ce front /\
  ss.cs_next_id <= front.cs_next_id /\ ss.cs_next_var <= front.cs_next_var ==>
  vv_holds_mods ce cx ty raw sv ee u /\ vv_at ce cx ty si ss ee raw sv u /\
  vv_storage_live H cx sv ee u
Proof
  strip_tac >>
  `wb_frame ce ee ee ss s u` by
    (qpat_assum `wb_frame ce ee ee front s u`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at front x` by
           (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `ss` >> simp[]) >>
         first_x_assum irule >> simp[]) >>
     rpt strip_tac >>
     `aid < front.cs_next_id` by simp[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
     first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `aid` >> simp[]) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee u`
    (mp_then Any assume_tac stmt_state_rel_state_rel) >>
  drule_then assume_tac state_rel_storage_rel >>
  drule_then assume_tac state_rel_transient_rel >>
  conj_tac
  >- (irule log_saved_linked_holds >> qexistsl [`H`,`s`,`si`,`ss`] >> simp[]) >>
  conj_tac
  >- (irule vv_at_alloc_map_frame >> qexistsl [`s`,`ss`] >> simp[] >>
      reverse conj_tac >- fs[wb_frame_def] >>
      rpt gen_tac >> irule local_region_wb_frame >>
      reverse conj_tac >- (qexistsl [`ee`,`front`] >> simp[]) >>
      qexists `func` >>
      qpat_assum `stmt_state_rel H ctx func ce cx ee s`
        (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
      first_assum ACCEPT_TAC) >>
  Cases_on `sv` >> gvs[vv_storage_live_def,vv_operand_def]
QED
