(* The delayed unwrap consumes the saved value at the actual target cut. *)
Theory bodyQualifiedPlaceRawUnwrapMods
Ancestors
  bodyQualifiedPlaceRhsPostMods bodySavedTargetVvPostMods bodySavedTargetPtrMods
  bodyWriteTargetStageMods loweringStateRelDefs exprSimProps immutableRegionFrameProps
  bodyFullShadowBodyInv ptrDiscipline bodyInvSplit valueCopyBytes assignBasePtrBoundary
  exprSimIfExpWidenedAdapter exprPtrUnwrapStorageShape allocLimits exprSimHyps
  bodySavedRhsSlotLiveMods bodyAssignLocalSavedMods bodyIfExpWordReadMods
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyCopyReadPhysicalTypeMods
  bodySlotCopySavedMods bodyCopySlotRhsEndpointMods bodyCopyMaterializedRhsPostMods
  bodyPtrSignedConvertSourceFrame exprSimWordArgs wordArgsPtr fragGasOriginPtrDead
  bodyLocalCopyPhysicalRhsMods exprOperandVar exprLoweringProps exprSimCopy
  vyperEvalExprPreservesScopesDom
  valueTypingMemoryProps bodyFullHashKeccakFixed
  exprLowering compileEnv bodyFullPostsMods loweringPosts bodyPtrDefs
  fragGasOriginPtr context stateRelProj vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageTrace bodyAssignQualifiedStageJoinMods finite_map words list
  bodyQualifiedPlaceTargetEntryMods stmtLoweringMono exprBodyPreTypingProps exprSimHypsDefs
  vyperTypeExtCallCore vyperTypeExprSoundness bodyMemoryDefs bodyFullTargetDefs venomState
  stmtSimLogCompose bodyFullIfExpReach fragGasPath


val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>``;

val cursor = ``
  unwrap_value ce vv k = (op,kf) /\ fn_has_code k kf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce k /\
  copy_old_operand k (vv_operand vv) /\
  ~s.vs_halted /\ s.vs_current_bb = k.cs_current_bb /\
  s.vs_inst_idx = LENGTH k.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s)``;

val saved_ptr = ``
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
           eval_operand (vv_operand vv) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)``;

val readonly = ``
    z = s with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP (Gf:string |-> num # num) x = FLOOKUP (G:string |-> num # num) x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

Theorem qualified_raw_word_run[local]:
  ^cursor /\ ^saved_ptr /\
  is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  read_result cx raw ee = (INL v,ee) /\ value_has_type rt v /\
  vv_post_mods H ctx func ce cx e ee sa k s ee raw vv s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s ==>
  ?z Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    eval_operand op z = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    z.vs_current_bb = kf.cs_current_bb /\ z.vs_inst_idx = LENGTH kf.cs_current_insts /\
    alloca_history func z /\ ^readonly
Proof
  strip_tac >> Cases_on `vv`
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def,comp_return_def] >> strip_tac >> gvs[] >>
      qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      qhdtm_x_assum `vv_holds_mods` mp_tac >>
      simp[vv_holds_mods_def,vv_holds_def,expr_val_rel_def] >> strip_tac >>
      qexistsl [`s`,`G`,`tn`] >>
      fs[ptr_vv_ok_def,ptr_val_ok_def,cj 1 gas_origin_ptr_path_rules]) >>
  rename1 `LocatedValue tag p` >>
  `tag = post_value_type ce e /\ p.ptr_location <> LocCalldata` by
    (drule word_arm_location >> simp[]) >>
  qpat_x_assum `tag = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `unwrap_value` mp_tac >> simp[unwrap_value_def] >> disch_tac >>
  qhdtm_assum `ghost_inv_at_mods`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`kf`,`rt`,`op`,`PG`] mp_tac) >>
  (impl_tac >- (gvs[vv_location_def,vv_operand_def] >> metis_tac[arithmeticTheory.ADD_COMM])) >>
  strip_tac >>
  `alloca_inv s` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at k x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at k x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `read_result cx raw ee = (INL vread,ee)` >>
  `vread = v` by
    (qpat_x_assum `read_result cx raw ee = (INL vread,ee)` mp_tac >> simp[]) >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

(* Rebase the open value, not its read, at the reached target endpoint. *)
Theorem qualified_raw_at_target[local]:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\ expr_sim_inv_mods mods ce cx env ee /\
  compile_expr ce (expr_type e) e sa = (vv,sr) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL v,mid) /\ read_result cx raw ee = (INL v,ee) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  local_ptrs_reserved ce sa /\ (!l. vv_operand vv <> Label l) /\
  stmt_state_rel H ctx func ce cx es s0 /\ storage_well_formed_on cx es (FST H) /\
  valid_horizon cx st0 H mid.storage_trace /\
  vv_post_mods H ctx func ce cx e es sa sr s0 mid raw vv u /\
  write_target_post_mods H D lo d ctx func ce cx bt mid sr k u ee
    (PlaceR place) (Type dty) dst Gu tu G tn s /\
  dead_lo_ok_mods H D lo ce cx /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) mid raw vv u /\
  ptr_vv_ok cx (post_value_type ce e) raw vv mid Gu tu u /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) Gu u) ==>
  vv_post_mods H ctx func ce cx e ee sa sr s ee raw vv s /\
  wb_frame ce es ee sa s0 s /\ ^saved_ptr /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) G s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac saved_rhs_slot_live_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sr x` by
    (drule (cj 1 compiler_compile_var) >> simp[]) >>
  drule_all_then strip_assume_tac saved_target_vv_post_mods >>
  `wb_frame ce mid mid sr u s` by
    (`ee.scopes = mid.scopes` by (qpat_assum `ee = _` (fn th => simp[Once th])) >>
     pop_assum (fn th => qpat_assum `wb_frame ce mid ee sr u s`
       (strip_assume_tac o PURE_REWRITE_RULE [wb_frame_def,locals_kept_def,popped_kept_def,th])) >>
     pure_rewrite_tac[wb_frame_def,locals_kept_def,popped_kept_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac saved_target_ptr_resources_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm_rewrite_tac[] >>
  `vv_holds_mods ce cx (post_value_type ce e) raw vv ee s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ ee _ _ _ ee _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >> first_assum ACCEPT_TAC) >>
  `(ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env ee /\
    dead_lo_ok_mods H D lo ce cx /\ ghost_inv_at_mods D lo d ce cx ee G tn s /\
    immutable_frame_mods func ce cx ee s /\
    vv_holds_mods ce cx (post_value_type ce e) raw vv ee s)` by simp[] >>
  drule_all_then strip_assume_tac assign_local_saved_ctor_source_mods >>
  first_assum ACCEPT_TAC
QED

Theorem qualified_raw_readonly_resources[local]:
  ^readonly /\ local_ptrs_reserved ce k /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  immutable_frame_mods func ce cx ee s /\ stmt_state_rel H ctx func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf z /\
  immutable_frame_mods func ce cx ee z /\ stmt_state_rel H ctx func ce cx ee z /\
  wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x cap. not_fresh_at k x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  `z.vs_memory = s.vs_memory /\ z.vs_call_ctx = s.vs_call_ctx /\
   z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_immutables = s.vs_immutables /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next /\ z.vs_data_section = s.vs_data_section` by
    (rpt conj_tac >> qpat_assum `z = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "immutable" >>
  conj_tac
  >- (irule stmt_state_rel_readonly_vars_pc >>
      qexistsl [`s`,`k`] >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (simp[wb_frame_def,locals_kept_mem] >> metis_tac[]) >>
  irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`,`tn`] >> simp[wordArgsPtrTheory.ghost_kept_at_refl] >> metis_tac[]
QED

Resume qualified_raw_readonly_resources[ghost]:
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at k p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Resume qualified_raw_readonly_resources[immutable]:
  simp[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutable_frame_mods_def,immutables_rel_mods_def,immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >>
  simp[] >> rpt strip_tac >> qexists `id` >>
  qmatch_asmsub_rename_tac `local_region (ce with ce_module := owner) _ _ _ _ _` >>
  `local_region (ce with ce_module := owner) ee.scopes z id b sz <=>
   local_region (ce with ce_module := owner) ee.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]) >>
  gs[]
QED

Finalise qualified_raw_readonly_resources

val all_posts = ``
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e ee sa k s ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s)``;

val suffix_entry = ``
  ^cursor /\ ^saved_ptr /\ ^all_posts /\ read_result cx raw ee = (INL v,ee) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x)``;

val suffix_frame = ``
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
  wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tf /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s) /\
  ~z.vs_halted /\ z.vs_current_bb = kf.cs_current_bb /\
  z.vs_inst_idx = LENGTH kf.cs_current_insts /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s.vs_alloca_next <= z.vs_alloca_next /\
  (!x. op = Var x ==> not_fresh_at kf x)``;

val word_value = ``
  ?rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    value_has_type rt v /\ eval_operand op z = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE``;

Theorem qualified_raw_word_suffix[local]:
  ^suffix_entry /\ is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\ value_has_type rt v ==>
  ?z Gf tf. ^suffix_frame /\ ^word_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all qualified_raw_word_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    immutable_frame_mods func ce cx ee z /\ stmt_state_rel H ctx func ce cx ee z /\
    wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     match_mp_tac qualified_raw_readonly_resources >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at_mods _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!x. op = Var x ==> not_fresh_at kf x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> fs[vv_operand_def,copy_old_operand_def]) >>
  `~z.vs_halted /\ z.vs_alloca_next = s.vs_alloca_next /\
   z.vs_allocas = s.vs_allocas /\ z.vs_fmp = s.vs_fmp /\ z.vs_initial_fmp = s.vs_initial_fmp` by
    (rpt conj_tac >> qpat_assum `z = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  qexistsl [`z`,`Gf`,`tf`] >> simp[] >>
  disch_tac >>
  qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
    (drule_then (strip_assume_tac o REWRITE_RULE [allocas_below_fmp_def])) >>
  simp[allocas_below_fmp_def] >> first_assum ACCEPT_TAC
QED

val copy_types = ``
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  value_has_type pt v /\ value_has_type rt v``;

val copy_value = ``
  ?rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type rt v /\ type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers Gf tf x z (type_memory_size rt)) /\
    (~is_bytestring_type (lowered_value_type ce e) ==>
      expr_val_at ce cx (lowered_value_type ce e) sa kf ee v op z)``;

Theorem qualified_raw_copy_value[local]:
  ^copy_types /\ expr_post_mods H ctx func ce cx e ee sa kf s ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
  (!w. eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
  ^copy_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def,expr_val_rel_def]) >>
  rename1 `eval_operand op z = SOME w` >>
  qexistsl [`rt`,`w`] >> asm_rewrite_tac[] >>
  `op_taint tf op = {} /\
   (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory pt v (w2n w) mem)` by
    fs[ptr_val_ok_def,ptr_mem_ok_def] >>
  `!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem` by
    metis_tac[bytestring_val_in_memory_transfer,optionTheory.SOME_11] >>
  `type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next` by simp[] >>
  `w2n w + type_memory_size rt < dimword (:256)` by
    (Cases_on `type_memory_size rt = 0` >- simp[w2n_lt] >>
     drule stmt_state_rel_alloca_room >> strip_tac >>
     drule_then assume_tac alloca_room_next_lt >> decide_tac) >>
  `(0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers Gf tf x z (type_memory_size rt))` by
    (disch_tac >> irule ptr_buf_ok_read_covers >> simp[] >>
     qexistsl [`ce`,`e`] >> simp[]) >>
  simp[] >> metis_tac[]
QED

val identity_shape = ``
  ((?tag. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
          ~is_word_type tag /\ p.ptr_operand = op))``;

Theorem qualified_raw_identity_suffix[local]:
  ^suffix_entry /\ ^copy_types /\ ^identity_shape /\ ptr_buf_ok ce e op G s ==>
  ?z Gf tf. ^suffix_frame /\ ^copy_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all_then (strip_assume_tac o SPEC_ALL) local_copy_rhs_identity_unwrap_mods >>
  `!w. eval_operand op s = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next` by
    (qpat_x_assum `!rt w. evaluate_type _ _ = SOME rt /\ _ ==> _`
       (qspec_then `rt` mp_tac) >> simp[]) >>
  drule_all_then assume_tac qualified_raw_copy_value >>
  qpat_x_assum `kf = k` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     fs[vv_post_mods_def]) >>
  `!x. op = Var x ==> not_fresh_at k x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> fs[vv_operand_def,copy_old_operand_def]) >>
  qexistsl [`s`,`G`,`tn`] >>
  simp[wb_frame_refl,wordArgsPtrTheory.ghost_kept_at_refl,cj 1 gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem qualified_raw_code_suffix[local]:
  ^suffix_entry /\ ^copy_types /\
  vv = LocatedValue tag p /\ p.ptr_location = LocCode /\
  post_value_type ce e = lowered_value_type ce e /\
  sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) ==>
  ?z Gf tf. ^suffix_frame /\ ^copy_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [vv_location_def,vv_operand_def,copy_old_operand_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ghost_kept_at lo ce ee sa G tn s G tn` by simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
  `(ce.ce_is_ctor ==> !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
      eval_operand p.ptr_operand s = SOME w ==> w2n w + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
    (qpat_x_assum `ce.ce_is_ctor /\ _ ==> _` mp_tac >> simp[]) >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size rt` by simp[] >>
  drule_all slot_copy_saved_code_unwrap_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!u. eval_operand op z = SOME u ==> type_memory_size rt = 0 \/
    w2n u + type_memory_size rt <= z.vs_alloca_next` by simp[] >>
  drule_all_then assume_tac qualified_raw_copy_value >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `!x. op = Var x ==> not_fresh_at kf x` by
    (drule compiler_unwrap_value_var >> fs[vv_operand_def]) >>
  qexistsl [`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Theorem qualified_raw_slot_suffix[local]:
  ^suffix_entry /\ ^copy_types /\
  vv = LocatedValue tag p /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  tag = post_value_type ce e /\ post_value_type ce e = lowered_value_type ce e /\
  type_memory_size rt < 2 ** 64 /\
  sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) ==>
  ?z Gf tf. ^suffix_frame /\ ^copy_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  qpat_x_assum `tag = post_value_type ce e` SUBST_ALL_TAC >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [vv_operand_def,copy_old_operand_def]) >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size rt` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all copy_slot_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `ghost_kept_at lo ce ee sa G tn s G tn` by simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e ee sa kf s ee v (Var root) z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tnf z /\
    ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tnf z /\
    ptr_buf_ok ce e (Var root) Gf z /\
    wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tnf /\
    not_fresh_at kf root` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     `type_memory_size rt <= type_memory_size rt /\
      type_memory_bytes ce (lowered_value_type ce e) <= type_memory_size rt` by simp[] >>
     drule_all_then strip_assume_tac copy_materialized_rhs_post_mods >>
     asm_rewrite_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!w. eval_operand (Var root) z = SOME w ==> type_memory_size rt = 0 \/
    w2n w + type_memory_size rt <= z.vs_alloca_next` by simp[] >>
  drule_all_then assume_tac qualified_raw_copy_value >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tnf z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qexistsl [`z`,`Gf`,`tnf`] >> asm_rewrite_tac[] >> simp[]
QED

Theorem qualified_raw_vv_end_mono[local]:
  vv_post_mods H ctx func ce cx e ee sa sr s ee raw vv s /\ sr.cs_next_id <= k.cs_next_id ==>
  vv_post_mods H ctx func ce cx e ee sa k s ee raw vv s
Proof
  simp[vv_post_mods_def] >> strip_tac >>
  conj_tac >- (irule vv_at_alloc_mono_frame >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  strip_tac >> irule vv_own_alloc_mono_frame >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem qualified_raw_located_tag[local]:
  vv_post_mods H ctx func ce cx e ee sa k s ee raw (LocatedValue tag p) s ==>
  p.ptr_location <> LocCalldata /\
  (tag = post_value_type ce e \/
   p.ptr_location = LocMemory /\ is_bytestring_type tag /\
   is_bytestring_type (post_value_type ce e))
Proof
  simp[vv_post_mods_def,vv_holds_mods_def,vv_holds_def] >>
  Cases_on `p.ptr_location` >> simp[] >> metis_tac[]
QED

Theorem qualified_raw_nonword_suffix[local]:
  ^suffix_entry /\ ^copy_types /\ compile_expr ce (expr_type e) e sa = (vv,sr) /\
  alloc_limits_expr ce e /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
    ptr_buf_ok ce e (vv_operand vv) G s) /\
  sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) ==>
  ?z Gf tf. ^suffix_frame /\ ^copy_value
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue tag p` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_then (CONJUNCTS_THEN2 assume_tac assume_tac) qualified_raw_located_tag >>
  Cases_on `p.ptr_location = LocMemory` >- suspend "memory" >>
  `tag = post_value_type ce e` by metis_tac[] >>
  `lowered_value_type ce e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type ce e = lowered_value_type ce e` by simp[post_value_type_lowered] >>
  Cases_on `p.ptr_location = LocCode` >- suspend "code" >>
  suspend "slot"
QED

Resume qualified_raw_nonword_suffix[stack]:
  rename1 `StackValue tag src` >>
  `src = op` by fs[unwrap_value_def,comp_return_def] >>
  qpat_x_assum `src = op` SUBST_ALL_TAC >>
  `ptr_buf_ok ce e op G s` by fs[vv_location_def,vv_operand_def] >>
  match_mp_tac (Q.INST [`vv` |-> `StackValue tag op`, `raw` |-> `raw`,
                        `pt` |-> `pt`, `rt` |-> `rt`] qualified_raw_identity_suffix) >>
  asm_rewrite_tac[] >> simp[]
QED

Resume qualified_raw_nonword_suffix[memory]:
  `~is_word_type tag` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `p.ptr_operand = op` by fs[unwrap_value_def,comp_return_def] >>
  `ptr_buf_ok ce e op G s` by fs[vv_location_def,vv_operand_def] >>
  match_mp_tac (Q.INST [`vv` |-> `LocatedValue tag p`, `raw` |-> `raw`,
                        `pt` |-> `pt`, `rt` |-> `rt`] qualified_raw_identity_suffix) >>
  asm_rewrite_tac[] >> simp[] >> qexists `p` >> simp[]
QED

Resume qualified_raw_nonword_suffix[code]:
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  irule qualified_raw_code_suffix >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Resume qualified_raw_nonword_suffix[slot]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  `type_memory_size rt < 2 ** 64` by
    (drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def] >> metis_tac[]) >>
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  irule qualified_raw_slot_suffix >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Finalise qualified_raw_nonword_suffix

(* The representative source read is selected once.  Changing the horizon
   does not change the saved operand, its ownership, or its source place. *)
Theorem qualified_raw_vv_horizon[local]:
  vv_post_mods (H0 : (bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es sa sr s0 mid raw vv u /\
  stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
  vv_storage_live H cx vv mid u ==>
  vv_post_mods H ctx func ce cx e es sa sr s0 mid raw vv u
Proof
  rw[vv_post_mods_def] >> first_x_assum irule >> simp[]
QED

val rhs_stage = ``
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods ce cx env bt e dty
       es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0) rhs_marks v mid Gu tu u``;

val target_stage = ``
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) ce cx st0 bt dty
    mid sr k dst u Gu tu target_marks place ee G tn s``;

val raw_components = ``
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL v,mid) /\
  vv_post_mods (H : (bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es sa sr s0 mid raw vv u /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) mid raw vv u /\
  ptr_vv_ok cx (post_value_type ce e) raw vv mid Gu tu u /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) Gu u)``;

Theorem qualified_raw_rhs_components[local]:
  ^rhs_stage /\ ~expr_can_mutate ce (target_to_expr bt) /\
  valid_horizon cx st0 H mid.storage_trace ==>
  compile_expr ce (expr_type e) e sa = (vv,sr) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sr x) /\
  ?gs raw. ^raw_components
Proof
  simp[qualified_assign_rhs_reached_mods_def] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [qualified_place_rhs_post_mods_def])) >>
  qpat_assum `assign_place_rhs_code_mods ce bt e sa = _`
    (mp_then (Pos hd) strip_assume_tac qualified_assign_rhs_code_view_mods) >> gvs[] >>
  qexistsl [`gs`,`pv`] >> asm_rewrite_tac[] >>
  rename1 `vv_location saved = NONE` >>
  Cases_on `saved` >> simp[vv_location_def,vv_operand_def]
QED

val entry_live = ``
  !H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ storage_well_formed_on cx es (FST H)``;

val raw_source = ``
  expr_sim_inv_mods mods ce cx env ee /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  (!r. read_result cx r mid = (INL v,mid) ==> read_result cx r ee = (INL v,ee))``;

Theorem qualified_raw_saved_at_cut[local]:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\ ^raw_source /\ ^entry_live /\
  ^rhs_stage /\ ^target_stage /\ ~expr_can_mutate ce (target_to_expr bt) /\
  sr.cs_next_id <= k.cs_next_id /\
  local_ptrs_reserved ce sa /\ (!l. vv_operand vv <> Label l) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> dead_lo_ok_mods H (DF H) lo ce cx) ==>
  compile_expr ce (expr_type e) e sa = (vv,sr) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sr x) /\
  value_runtime_typed env (expr_type e) v /\
  ?gs raw. eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
    read_result cx raw mid = (INL v,mid) /\ read_result cx raw ee = (INL v,ee) /\
    ^all_posts /\ ^saved_ptr /\
    ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
      vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) G s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (strip_assume_tac o BETA_RULE) qualified_place_rhs_entry_view_mods >>
  qpat_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  `mid with gas_obs := [] = mid /\ ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `eval_target_place _ _ _ = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     simp[] >>
     qpat_assum `bind (eval_expr _ _) _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac qualified_raw_rhs_components >>
  qmatch_asmsub_rename_tac `eval_expr cx e (es with gas_obs := gs) = (INL raw,mid)` >>
  `read_result cx raw ee = (INL v,ee)` by simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e ee sa k s ee raw vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\ ^saved_ptr /\
     ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
       vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) G s)` by
    (gen_tac >> disch_tac >> suspend "at_horizon") >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`gs`,`raw`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume qualified_raw_saved_at_cut[at_horizon]:
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> valid_horizon _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `vv_storage_live H cx vv mid u` by
    (qpat_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos hd) mp_tac qualified_raw_rhs_components) >>
     disch_then (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
     rename1 `eval_expr cx e (es with gas_obs := hs) = (INL r,mid)` >>
     drule_at (Pat `eval_expr cx e (es with gas_obs := hs) = (INL r,mid)`)
       saved_rhs_slot_live_mods >> simp[] >> disch_then irule >>
     qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ r _ _` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `vv_post_mods H ctx func ce cx e es sa sr s0 mid raw vv u` by
    (irule qualified_raw_vv_horizon >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> dead_lo_ok_mods _ _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  drule_all_then strip_assume_tac qualified_raw_at_target >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule qualified_raw_vv_end_mono >> qexists `sr` >> simp[]
QED

Finalise qualified_raw_saved_at_cut

val value_landing = ``if is_word_type (expr_type e) then ^word_value else ^copy_value``;

Theorem qualified_raw_run_suffix[local]:
  ^suffix_entry /\ expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL v,mid) /\ value_runtime_typed env (expr_type e) v /\
  compile_expr ce (expr_type e) e sa = (vv,sr) /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type ce e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok ce e (vv_operand vv) G s) /\
  sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) ==>
  ?z Gf tf. ^suffix_frame /\ ^value_landing
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `is_word_type (expr_type e)`
  >- (drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac runtime_consistent_get_tenv >>
      qhdtm_x_assum `value_runtime_typed` (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
      `is_word_type (post_value_type ce e)` by simp[] >>
      rename1 `evaluate_type env.type_defs (expr_type e) = SOME rt` >>
      `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt` by simp[] >>
      qpat_assum `is_word_type (expr_type e)`
        (fn th => pure_rewrite_tac [EQT_INTRO th,COND_CLAUSES]) >>
      match_mp_tac (Q.INST [`raw` |-> `raw`,`rt` |-> `rt`,`vv` |-> `vv`]
        qualified_raw_word_suffix) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
    simp[Once bind_def] >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))
    copy_read_physical_type_gas_obs_mods >>
  `alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==>
    ptr_buf_ok ce e (vv_operand vv) G s` by
    (qpat_x_assum `_ \/ _ ==> ptr_buf_ok ce e _ G s` mp_tac >> simp[]) >>
  qpat_assum `~is_word_type (expr_type e)`
    (fn th => pure_rewrite_tac [EQF_INTRO th,COND_CLAUSES]) >>
  match_mp_tac (Q.INST [`raw` |-> `raw`,`pt` |-> `pt`,`rt` |-> `rt`,
    `vv` |-> `vv`,`sr` |-> `sr`] qualified_raw_nonword_suffix) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val dst_equations = ``
  eval_operand (FST (dst : operand # data_location option # place_ty option)) z = eval_operand (FST dst) s /\
  op_prov Gf (FST dst) = op_prov G (FST dst) /\
  op_taint tf (FST dst) = op_taint tn (FST dst)``;

Theorem qualified_raw_dest_fields[local]:
  (!l. FST dst <> Label l) /\ (!x. FST dst = Var x ==> not_fresh_at k x) /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s) /\
  ghost_kept_at lo ce ee k G tn s Gf tf ==> ^dst_equations
Proof
  strip_tac >> Cases_on `FST dst` >> fs[eval_operand_def,op_prov_def,op_taint_def,ghost_kept_at_def] >>
  metis_tac[]
QED

Theorem qualified_raw_dest_location[local]:
  ^dst_equations /\
  ((?tr slot tv. place = StoragePlace tr slot tv) \/ (?path. place = ImmutablePlace owner id path)) /\
  target_ptr_ok ce (PlaceR place) dst G tn s /\
  write_target_location_mods ce cx bt ee (PlaceR place) (Type dty) dst G s ==>
  target_ptr_ok ce (PlaceR place) dst Gf tf z /\
  write_target_location_mods ce cx bt ee (PlaceR place) (Type dty) dst Gf z
Proof
  strip_tac >> gvs[target_ptr_ok_def,write_target_location_mods_def,place_ptr_rel_def] >>
  metis_tac[]
QED

val from_entry = ``
  wb_frame ce es ee sa s0 z /\
  ghost_kept_at lo ce es sa (G0 : string |-> num # num) tn0 s0 Gf tf /\
  alloca_frame ce es sa s0 ce ee z /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  s0.vs_alloca_next <= z.vs_alloca_next /\ return_buf_frame d ce kf z /\
  local_ptrs_reserved ce kf /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at kf x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at kf x)``;

Theorem qualified_raw_extend_frame[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce k /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id /\
  k.cs_next_var <= kf.cs_next_var /\
  wb_frame ce es ee sa s0 s /\ wb_frame ce ee ee k s z /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ ghost_kept_at lo ce ee k G tn s Gf tf /\
  return_buf_frame d ce k s /\ s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s) /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at k x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at k x) ==>
  ^from_entry
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_asm1_tac
  >- (qpat_assum `stmt_state_rel H _ _ _ _ es s0`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule wb_frame_trans) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H _ _ _ _ es s0`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
      qpat_assum `ghost_kept_at _ _ ee k _ _ s _ _` (irule_at Any) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac
  >- (drule log_wb_alloca_frame >> disch_then irule >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`k`] >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `k` >> simp[]) >>
  conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists `k` >> simp[]
QED

(* The endpoint and unwrap instruction interval are those of the caller's
   reached qualified Assign. Read agreement is a source-side input. *)
Theorem qualified_place_raw_unwrap_mods:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods ce cx env se ==>
    expr_body_pre_mods mods ce cx env i se) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\ ^entry_live /\
  qualified_assign_code_mods ce bt e sa sb shadow_sa shadow_sb (SOME vv) sr k
    shadow_sr shadow_k dst /\ ^rhs_stage /\ ^target_stage /\
  ~expr_can_mutate ce (target_to_expr bt) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  (!r. read_result cx r mid = (INL v,mid) ==> read_result cx r ee = (INL v,ee)) /\
  (!l. vv_operand vv <> Label l) /\ (!l. FST dst <> Label l) /\
  unwrap_value ce vv k = (op,kf) /\ fn_has_code k kf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> dead_lo_ok_mods H (DF H) lo ce cx) ==>
  ?z Gf tf. ^suffix_frame /\ ^value_landing /\ ^dst_equations /\ ^from_entry /\
    (!x. FST dst = Var x ==> not_fresh_at kf x) /\
    target_ptr_ok ce (PlaceR place) dst Gf tf z /\
    write_target_location_mods ce cx bt ee (PlaceR place) (Type dty) dst Gf z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> storage_well_formed_on cx ee (FST H))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by simp[] >>
  qpat_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_store_frame_mods >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `sr.cs_next_var <= k.cs_next_var /\ sr.cs_next_id <= k.cs_next_id` by
    (qspecl_then [`bt`,`ce`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[ci_mono_def]) >>
  `k.cs_next_var <= kf.cs_next_var` by
    (qspecl_then [`ce`,`vv`,`k`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  drule_all_then strip_assume_tac qualified_raw_saved_at_cut >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `sa.cs_next_var <= k.cs_next_var /\ sa.cs_next_id <= k.cs_next_id` by decide_tac >>
  `copy_old_operand k (vv_operand vv)` by
    (simp[copy_old_operand_def] >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sr` >> simp[]) >>
  drule_all qualified_raw_run_suffix >>
  disch_then (qspecl_then [`explicit`,`PG`] (strip_assume_tac o BETA_RULE)) >>
  suspend "landing"
QED

Resume qualified_place_raw_unwrap_mods[landing]:
  drule_all_then strip_assume_tac qualified_raw_dest_fields >>
  `target_ptr_ok ce (PlaceR place) dst Gf tf z /\
   write_target_location_mods ce cx bt ee (PlaceR place) (Type dty) dst Gf z` by
    (match_mp_tac (Q.INST [`s` |-> `s`,`G` |-> `G`,`tn` |-> `tn`,
      `owner` |-> `owner`,`id` |-> `id`] qualified_raw_dest_location) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_x_assum `(?tr slot tv. place = StoragePlace tr slot tv /\ _) \/ _` mp_tac >>
     strip_tac >> simp[]) >>
  drule_all_then strip_assume_tac qualified_raw_extend_frame >>
  `!x. FST dst = Var x ==> not_fresh_at kf x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `k` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> storage_well_formed_on cx ee (FST H)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_then strip_assume_tac write_target_post_view_mods >> first_assum ACCEPT_TAC) >>
  qexistsl [`z`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise qualified_place_raw_unwrap_mods
