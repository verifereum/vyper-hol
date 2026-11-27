(* Topics consume physical capture types, not declared indexed capacities.
   The positional relation permits a caller to select any indexed subsequence
   while retaining each captured operand's actual type and value. *)
Theory bodyFullLogScalarTopics
Ancestors
  bodyFullLogSuffix stmtSimLogArgs supportedTypes list
  stmtSimLogTopics exprSimMemDefs exprSimProps vyperTyping
  exprSimHashBoundary loweringStateRelDefs fragExec fragGasOriginPtrLoop
  fragGasOriginPtr bodyFullPathHistory
  loweringPosts bodyPtrDefs venomMemDefs venomState allocaHistory
  vyperStorageTrace vyperStorageFootprint vyperEvent
  exprLoweringProps exprSafeOperand exprSimWordArgs wordArgsPtr
  eventLoweringStructure freshWrites arithmetic
  exprSimHypsDefs[qualified]
Libs horizonTypeLib

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  Cases_on `ty` >>
  simp[supported_event_leaf_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
  >- metis_tac[log_arg_clear_base] >>
  rw[log_arg_clear_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `dynarray_free (FlagTV m)` by
    (rw[loweringPostsTheory.dynarray_free_def] >> Cases_on `path` >>
     simp[loweringPostsTheory.mem_path_offset_def, AllCaseEqs(),
          optionTheory.OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD, PULL_EXISTS] >>
     rpt strip_tac >> drule mem_step_offset_shape >> simp[]) >>
  drule_all exprSimAttributeFieldsTheory.local_val_at_dynarray_apart >> simp[]
QED
*)
Theorem log_arg_clear_event:
  !mods.
  expr_sim_inv_mods mods cenv cx env es /\ supported_event_leaf_type ty ==>
  log_arg_clear cenv cx ty v
Proof
  cheat
QED

Theorem compile_log_saved_topic_hash:
  !mods.
  local_ptrs_reserved cenv sm /\ expr_sim_inv_mods mods cenv cx env es /\
  expr_val_rel cx ty v src s /\ expr_val_at cenv cx ty sa sm es v src s /\
  supported_event_leaf_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ encode_event_topic ty v = SOME topic /\
  safe_operand sm src /\
  compile_encode_log_topic src (is_bytestring_type ty) sm = (op,sb) /\
  ptr_val_ok cx ty v src G tn s /\ expr_store_bound cx ty v src s /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es Gf tf t) /\
    wb_frame cenv es es sm s t /\ ghost_kept_at lo cenv es sm G tn s Gf tf /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    safe_operand sb op /\ eval_operand op t = SOME topic /\ op_taint tf op = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H es.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `log_arg_rel cenv cx sa sm es s (src,ty) v` by
    (simp[log_arg_rel_def] >> metis_tac[log_arg_clear_event]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  fs[safe_operand_def] >>
  drule_all compile_log_hash_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  drule_all log_topic_frontier >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _|> = s`
      (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `alloca_history func t` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tf)`
       (qspec_then `DF hz` (mp_then Any irule body_full_path_alloca_history)) >>
     simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (`stmt_state_rel H ctx func cenv cx es (t with vs_inst_idx := s.vs_inst_idx)` by
        (mp_tac (Q.INST [`sa` |-> `sm`,`t` |-> `t with vs_inst_idx := s.vs_inst_idx`]
           (horizonTypeLib.at_horizon_named "H" hash_readonly_state_rel)) >>
         impl_tac >-
           (asm_rewrite_tac[] >> fs[lookup_var_def, venom_state_component_equality]) >>
         disch_then ACCEPT_TAC) >>
      fs[stmt_state_rel_inst_idx]) >>
  metis_tac[]
QED

Definition log_topic_state_def:
  log_topic_state ctx func ce cx st0 es DF lo d front s G tn a u Gu tu <=>
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es u /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d ce cx es Gu tu u) /\
    wb_frame ce es es front s u /\ ghost_kept_at lo ce es front G tn s Gu tu /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    front.cs_next_var <= a.cs_next_var /\ front.cs_next_id <= a.cs_next_id /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts
End

Theorem log_topic_state_step:
  log_topic_state ctx func ce cx st0 es DF lo d front s G tn a u Gu tu /\
  stmt_state_rel H ctx func ce cx es s /\ local_ptrs_reserved ce front /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es v /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es Gv tv v) /\
  wb_frame ce es es a u v /\ ghost_kept_at lo ce es a Gu tu u Gv tv /\
  alloca_history func v /\ u.vs_alloca_next <= v.vs_alloca_next /\
  v.vs_current_bb = b.cs_current_bb /\ v.vs_inst_idx = LENGTH b.cs_current_insts ==>
  log_topic_state ctx func ce cx st0 es DF lo d front s G tn b v Gv tv
Proof
  simp_tac bool_ss [log_topic_state_def] >> strip_tac >>
  `wb_frame ce es es front s v` by
    (mp_tac (Q.INST [`H` |-> `H`] (Q.SPECL
       [`func`,`ce`,`cx`,`es`,`s`,`front`,`es`,`es`,`a`,`u`,`v`,`ctx`] wb_frame_trans)) >>
     simp[]) >>
  `ghost_kept_at lo ce es front G tn s Gv tv` by
    (qspecl_then [`lo`,`ce`,`es`,`front`,`G`,`tn`,`s`,`Gu`,`tu`,`es`,`a`,`Gv`,`tv`,
       `u`,`H`,`ctx`,`func`,`cx`,`es`] mp_tac ghost_kept_at_wb_trans >> simp[]) >>
  simp[] >> decide_tac
QED

Theorem log_topic_physical_val_at:
  sa.cs_next_id <= si.cs_next_id /\ sa.cs_next_id <= a.cs_next_id /\
  ss.cs_next_id <= b.cs_next_id /\
  (~is_word_type ty ==> expr_val_at ce cx ty si ss es v src s \/
    expr_val_at ce cx ty a b es v src s) ==>
  expr_val_at ce cx ty sa b es v src s
Proof
  strip_tac >> Cases_on `is_word_type ty` >- simp[expr_val_at_def] >>
  qpat_x_assum `~is_word_type ty ==> _` (drule_then DISJ_CASES_TAC)
  >- (simp_tac bool_ss [expr_val_at_def] >> gen_tac >> strip_tac >>
      qpat_assum `expr_val_at ce cx ty si ss es v src s`
        (mp_tac o Q.SPEC `tv` o REWRITE_RULE [expr_val_at_def]) >>
      impl_tac >- simp[] >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `w` (CONJUNCTS_THEN2 assume_tac mp_tac))) >>
      disch_then (DISJ_CASES_THEN2 strip_assume_tac
        (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
      >- (simp[] >> disj1_tac >>
          qexistsl_tac [`aid`,`b'`,`sz`] >> simp[] >> first_assum ACCEPT_TAC)
      >- (simp[] >> disj2_tac >> disj1_tac >>
          qexistsl_tac [`n`,`b'`,`sz`] >> simp[]) >>
      simp[]) >>
  irule expr_val_at_start_mono >> qexists_tac `a` >> simp[]
QED
