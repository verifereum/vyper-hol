(* The captured storage or transient slot at the array-index cut. *)
Theory bodyFullSubscriptLiveSlotSelect
Ancestors
  accountsRelProps stmtSimAugAssignPlaceStorage vyperStorageFootprint
  vyperStorageWritePreservation loweringStateRelDefs
  bodyFullSubscriptExprSlotRegion bodyFullSubscriptPopSlotRegion
  gasOutcomeFull vyperStorageTrace bodyFullSubscriptObservedSlotPtr
  bodyFullSubscriptSlotRun exprSimSubscriptArrayLiveStorageElement
  exprSimSubscriptArrayLiveStorageEndpoint exprSimSubscriptArraySuffix
  exprSimSubscriptArraySource exprSimSource exprOperandVar vyperTypeConstantFold
  exprSimHypsDefs loweringPosts bodyPtrDefs gasExplicitSites stateRelProj
  bodyFullAllocaFresh bodyFullUnwrapRun wordArgsPtr
  context compileEnv exprReasonOperand exprSimHyps
  exprSimFieldLayout exprSimWordArgs exprBopSimProps freshWrites targetSubscriptStorage
  vyperTypeValues[qualified,ignore_grammar] bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem subscript_slot_root_after_index[local]:
  well_typed_expr env obj /\ runtime_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr obj) /\
  eval_expr cx obj st = (INL (PlaceR (StoragePlace tr slot vt)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  storage_well_formed_on cx st (FST H) /\
  valid_horizon cx st0 H fin.storage_trace ==>
  ?off root path delta.
    MEM (StorageRoot tr off root) fin.storage_trace /\
    storage_subregion root path delta vt /\ slot = n2w off + n2w delta
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `storage_trace_frame (bind (eval_expr cx idx) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `?evs. fin.storage_trace = mid.storage_trace ++ evs` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule valid_horizon_append >> qexists `evs` >> fs[]) >>
  `?off root path delta.
    MEM (StorageRoot tr off root) mid.storage_trace /\
    storage_subregion root path delta vt /\ slot = n2w off + n2w delta` by
    (irule (Q.SPEC `H` subscript_expr_result_slot_region_from_pop) >>
     fs[valid_horizon_def] >>
     metis_tac[subscript_pop_result_slot_region]) >>
  qexistsl [`off`,`root`,`path`,`delta`] >> simp[listTheory.MEM_APPEND]
QED

Theorem traced_subscript_base_live[local]:
  valid_horizon cx st0 H fin.storage_trace /\
  storage_well_formed_on cx fin (FST H) /\
  MEM (StorageRoot tr offset root) fin.storage_trace /\
  storage_subregion root path delta leaf /\ slot = n2w offset + n2w delta ==>
  storage_read_live H tr (get_storage cx fin tr) slot leaf /\
  slots_in_range (get_storage cx fin tr) (w2n slot) leaf
Proof
  strip_tac >> Cases_on `type_slot_size leaf = 0`
  >- (simp[storage_read_live_def, zero_slot_size_slots_in_range] >>
      rpt strip_tac >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
      simp[wordsTheory.w2n_lt]) >>
  `storage_place_observed H (StoragePlace tr slot leaf)` by
    metis_tac[aug_place_storage_rooted_observed] >>
  conj_tac >- (irule storage_place_observed_read_live >> simp[]) >>
  irule aug_place_observed_slots_in_range >>
  conj_tac >- decide_tac >>
  qexists_tac `H` >> fs[valid_horizon_def]
QED

Theorem subscript_live_slot_select_full:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
  post_value_type cenv obj = expr_type obj /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  lower_value compile_expr cenv ty idx sm = (iop,sn) /\
  loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) sn = (dst,sb) /\
  fn_has_code sn sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (StoragePlace tr slot vt)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func u /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv obj) (PlaceR (StoragePlace tr slot vt)) bvv mid G1 tn1 s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni u /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    vv_post H ctx func cenv cx obj es sa sm s0 mid (PlaceR (StoragePlace tr slot vt)) bvv s /\
    expr_post H ctx func cenv cx idx mid sm sn s fin key iop u /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni u) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et bd) (PlaceR (StoragePlace tr slot vt)) (ValueSubscript key))
    (fin,u,Gi,tni)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      vv_store_bound cx (post_value_type cenv (Subscript ann obj idx))
        (lowered_value_type cenv (Subscript ann obj idx)) ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx)) tv (LocatedValue ann (mk_ptr dst loc)) ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann obj idx)) /\
           ~is_bytestring_type (post_value_type cenv (Subscript ann obj idx)) ==>
           vv_own cenv cx (post_value_type cenv (Subscript ann obj idx)) sa sb ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
           (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr dst loc)) = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann obj idx)) =
                    SOME rt /\ eval_operand (vv_operand (LocatedValue ann (mk_ptr dst loc))) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. (LocatedValue ann (mk_ptr dst loc)) = StackValue t' op /\
               ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
               ptr_buf_ok cenv (Subscript ann obj idx) op G t) /\
      (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv (Subscript ann obj idx) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  (* the base may be a huge slot base, whose own precondition the parent's
     does not give: take what is used from the parent's *)
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs1)` by simp[] >>
  `expr_sim_inv cenv cx env mid /\
   eval_result_typed (env,cx,mid) (PlaceR (StoragePlace tr slot vt))
     (Type (expr_type obj))` by metis_tac[expr_sim_inv_eval_result] >>
  `env_consistent env cx (es with gas_obs := gs1) /\
   runtime_consistent env cx (es with gas_obs := gs1) /\ functions_well_typed cx` by
    (qpat_assum `expr_sim_inv _ _ _ (es with gas_obs := _)`
       (mp_tac o PURE_REWRITE_RULE [expr_sim_inv_def]) >>
     PURE_REWRITE_TAC [vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv] >>
  `?etv. vt = ArrayTV etv bd /\ evaluate_type (get_tenv cx) et = SOME etv /\
      evaluate_type (get_tenv cx) (ArrayT et bd) = SOME vt /\
      well_formed_type_value vt` by
    (`evaluate_type (get_tenv cx) (ArrayT et bd) = SOME vt /\ well_formed_type_value vt` by
       (qpat_x_assum `eval_result_typed _ (PlaceR _) _` mp_tac >>
        simp[vyperPlaceResultTypingTheory.eval_result_typed_place,
             vyperPlaceTypingTheory.runtime_place_typed_storage]) >>
     drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
     metis_tac[]) >>
  `?bt p. bvv = LocatedValue bt p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand s = SOME slot` by
    (`post_value_type cenv obj = ArrayT et bd` by metis_tac[] >>
     Cases_on `bvv` >>
     qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [vv_post_def, vv_at_def, vv_holds_def, vv_place_ptr_def]) >>
     simp[is_word_type_def, SF CONJ_ss] >> metis_tac[]) >>
  `ann = et` by
    (`well_typed_expr env (Subscript ann obj idx)` by fs[expr_body_pre_def] >>
     drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    ?off root path delta. MEM (StorageRoot tr off root) fin.storage_trace /\
      storage_subregion root path delta vt /\ slot = n2w off + n2w delta` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     irule subscript_slot_root_after_index >>
     qexistsl [`H`,`cx`,`env`,`gs2`,`idx`,`key`,`mid`,`obj`,
               `es with gas_obs := gs1`,`st0`] >> simp[] >>
     `!b. get_storage cx (es with gas_obs := gs1) b = get_storage cx es b` by
       (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     fs[storage_well_formed_on_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    storage_place_observed H (StoragePlace tr slot vt) /\
    storage_read_live H tr (get_storage cx fin tr) slot vt /\
    slots_in_range (get_storage cx fin tr) (w2n slot) vt` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ?off root path delta. _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     `storage_well_formed_on cx fin (FST H)` by fs[expr_post_def] >>
     conj_tac >- metis_tac[aug_place_storage_rooted_observed] >>
     irule traced_subscript_base_live >> simp[] >> metis_tac[]) >>
  `?tvi. evaluate_type (get_tenv cx) (expr_type idx) = SOME tvi /\
         value_has_type tvi key` by
    (`expr_body_pre cenv cx env (Subscript ann obj idx) (es with gas_obs := gs1)` by simp[] >>
     drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
     `?ir. eval_expr cx idx (mid with gas_obs := gs2) = (INL ir,fin) /\
           read_result cx ir fin = (INL key,fin)` by
       (drule_then strip_assume_tac vyperStatePreservationTheory.bind_split
        >- (rename1 `read_result cx ir _ = (INL key,fin)` >>
            qpat_assum `read_result cx ir _ = _`
              (SUBST_ALL_TAC o MATCH_MP vyperStateTheory.read_result_state) >>
            qexists `ir` >> simp[])
        >> gvs[]) >>
     `expr_body_pre cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
     drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
     metis_tac[]) >>
  drule_all_then strip_assume_tac framed_array_index_post_view >>
  `loc = slot_loc tr /\ vv_operand bvv = p.ptr_operand` by
    simp[vv_operand_def, vv_location_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. iop = Var x ==> not_fresh_at sn x` by
    metis_tac[compile_lower_value_var] >>
  `!l. p.ptr_operand <> Label l` by
    (`!id t. FLOOKUP env.var_types id = SOME t ==>
        ?x sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz)` by
       (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
        rewrite_tac[expr_sim_inv_def] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
     `reason_uniform_shape compile_expr cenv ty obj` by
       (irule compile_expr_reason_uniform >> metis_tac[]) >>
     qpat_x_assum `reason_uniform_shape _ _ _ _` mp_tac >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> simp[reason_result_shape_def]) >>
  `wb_frame cenv mid fin sm s u` by
    (qpat_assum `expr_post H0 _ _ _ _ idx _ _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP expr_post_frame) >> simp[]) >>
  `eval_operand p.ptr_operand u = SOME slot` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl [`sm`,`s`] >> fs[wb_frame_def]) >>
  `op_taint tn1 p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `op_taint tni p.ptr_operand = {}` by
    (Cases_on `p.ptr_operand` >> gvs[ghost_kept_at_def] >>
     try (rpt (CHANGED_TAC (simp[ptrDisciplineTheory.op_taint_def]))) >>
     metis_tac[]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> simp[] >>
     qexistsl [`cx`,`env`,`es`] >> gvs[expr_body_pre_def]) >>
  `word_scale loc = 1 /\ elem_size_in_location cenv loc et = type_slot_size etv` by
    (Cases_on `tr` >>
     fs[slot_loc_def, word_scale_def, elem_size_in_location_def,
        is_slot_addressed_def, slot_count_of_memory_size]) >>
  `is_int_type (expr_type idx)` by
    (`well_typed_expr env (Subscript ann obj idx)` by fs[expr_body_pre_def] >>
     pop_assum mp_tac >>
     simp[Once (cj 7 vyperTypeSystemTheory.well_typed_expr_def)] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >>
     rename1 `type_place_expr env obj = SOME pty` >>
     strip_tac >> Cases_on `pty` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
     rename1 `is_word_type (BaseT ibt)` >> Cases_on `ibt` >>
     gvs[vyperTypeSystemTheory.is_int_type_def, is_word_type_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> storage_place_observed H _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ptr_vv_ok cx (ArrayT et bd) (PlaceR (StoragePlace tr slot vt)) bvv fin Gi tni u` by
    (gvs[] >> irule subscript_observed_slot_ptr_at >> simp[] >>
     qexistsl [`DF H0`,`H0`,`cenv`,`d`,`lo`] >> simp[]) >>
  `(case bd of Fixed _ => F | Dynamic _ => T) ==>
   key_taint (if tr then tni.t_trans else tni.t_stor) slot = {}` by
    (Cases_on `bd` >> gvs[] >>
     qpat_assum `ptr_vv_ok _ _ _ (LocatedValue _ _) fin Gi tni u`
       (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [ptr_vv_ok_def]) >>
     `p.ptr_location = slot_loc tr` by
       (qpat_assum `slot_loc tr = _` mp_tac >> simp[NoAsms, vv_location_def]) >>
     `w2n slot < w2n slot + type_slot_size (ArrayTV etv (Dynamic n))` by
       simp[vyperValueTheory.type_slot_size_def] >>
     Cases_on `tr` >>
     simp[ptrDisciplineTheory.key_taint_def, pred_setTheory.EXTENSION] >>
     gen_tac >> rename1 `b < 32` >>
     Cases_on `b < 32` >> simp[] >> CCONTR_TAC >>
     qpat_x_assum `p.ptr_location = case _ of NONE => _ | SOME _ => _` kall_tac >>
     gvs[slot_loc_def] >>
     qpat_x_assum `!k b'. _` (qspecl_then [`slot`,`b`] mp_tac) >>
     simp[] >> strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]) >>
  qpat_x_assum `loc = case _ of NONE => _ | SOME _ => _` kall_tac >>
  qabbrev_tac `dyn = case bd of Fixed _ => F | Dynamic _ => T` >>
  qabbrev_tac `cnt = case bd of Fixed n => n | Dynamic _ => 0` >>
  qabbrev_tac `nw = if dyn then (if tr then tload slot u else sload slot u) else n2w cnt` >>
  `compile_array_subscript p.ptr_operand iop dyn cnt 1 (type_slot_size etv)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)) sn = (dst,sb)` by
    fs[] >>
  `stmt_state_rel H0 ctx func cenv cx fin u` by
    (qpat_assum `expr_post H0 _ _ _ _ idx _ _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP expr_post_state) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule subscript_slot_array_execution >>
  disch_then (qspecl_then [`u`,`tni`,`slot`,`nw`,`lo`,`iw`,`func`,
      `gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`,`Gi`] mp_tac) >>
  impl_tac >- simp[Abbr `nw`] >>
  disch_then (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tnq`
    (map_every assume_tac o CONJUNCTS)))) >>
  `bound_length bd < dimword (:256)` by
    metis_tac[target_storage_array_type_bound] >>
  `w2n slot + type_slot_size vt <= dimword (:256)` by
    (Cases_on `type_slot_size vt = 0` >-
       simp[arithmeticTheory.LESS_IMP_LESS_OR_EQ, wordsTheory.w2n_lt] >>
     qpat_assum `storage_place_observed H0 _`
       (strip_assume_tac o PURE_REWRITE_RULE
         [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     rename1 `storage_subregion tv path delta vt` >>
     rename1 `slot = root + n2w delta` >>
     drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
     `w2n root + type_slot_size tv <= dimword (:256)` by
       metis_tac[valid_horizon_def, regions_consistent_def] >>
     gvs[] >>
     `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  `idx_in_range (is_signed_type (expr_type idx)) iw nw <=>
   0 <= i /\ Num i < bound_length bd /\
   (dyn ==> Num i < w2n (lookup_storage slot (get_storage cx fin tr)))` by
    (qpat_x_assum `i = if _ then _ else _` (assume_tac o SYM) >>
     Cases_on `bd` >> gvs[Abbr `nw`, Abbr `dyn`, Abbr `cnt`] >-
       (simp[idx_in_range_integer, SF CONJ_ss] >>
        metis_tac[integerTheory.INT_OF_NUM, integerTheory.INT_LT]) >>
     `w2n (lookup_storage slot (get_storage cx fin tr)) <= n` by
       fs[vyperLookupStorageTheory.slots_in_range_def, vyperStorageTheory.read_slot_def,
          AllCaseEqs()] >>
     `(if tr then tload slot u else sload slot u) =
         lookup_storage slot (get_storage cx fin tr)` by
       (`storage_read_live H0 tr (get_storage cx fin tr) slot (ArrayTV etv (Dynamic n))` by simp[] >>
        `w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword (:256)` by decide_tac >>
        drule_all (cj 2 target_storage_array_len_ok) >> simp[]) >>
     simp[] >>
     qabbrev_tac `lw = lookup_storage slot (get_storage cx fin tr)` >>
     qmatch_goalsub_abbrev_tac `0 <= (j:int)` >>
     `idx_in_range (is_signed_type (expr_type idx)) iw lw <=>
      0 <= j /\ j < &w2n lw` by
       (`w2n lw < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
        drule_then (mp_tac o REWRITE_RULE [wordsTheory.n2w_w2n]) idx_in_range_integer >>
        simp[Abbr `j`]) >>
     `0 <= j /\ j < &w2n lw <=> 0 <= j /\ Num j < w2n lw` by
       metis_tac[integerTheory.INT_OF_NUM, integerTheory.INT_LT] >>
     gvs[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[LET_THM] >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw nw`) >-
    (`?msg. !tail.
        select_result cx (ArrayT et bd) (PlaceR (StoragePlace tr slot vt))
          (ValueSubscript key) (fin with gas_obs := tail) =
        (INR (Error (RuntimeError msg)), fin with gas_obs := tail)` by
       (`!tail. get_storage cx (fin with gas_obs := tail) tr = get_storage cx fin tr` by
          (Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
        qpat_x_assum `vt = _` SUBST_ALL_TAC >>
        qpat_x_assum `key = _` SUBST_ALL_TAC >>
        qpat_x_assum `i = if _ then _ else _` kall_tac >>
        Cases_on `bd` >-
          (gvs[Abbr `dyn`] >> qexists `"array fixed oob"` >>
           simp[vyperStateTheory.select_result_def, extend_place_storage_array_index]) >>
        `~(0 <= i /\ Num i < n /\ Num i < w2n (lookup_storage slot (get_storage cx fin tr)))` by
          fs[Abbr `dyn`] >>
        Cases_on `0 <= i /\ Num i < n` >-
          (qexists `"array dynamic length oob"` >>
           gvs[vyperStateTheory.select_result_def, extend_place_storage_array_index]) >>
        qexists `"array dynamic capacity oob"` >>
        gvs[vyperStateTheory.select_result_def, extend_place_storage_array_index]) >>
     irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
     conj_tac >-
       (qexistsl [`Gq`,`fin`,`Abort Revert_abort q`,`INR (Error (RuntimeError msg))`,`tnq`] >>
        gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def,
            fragExecTheory.exit_result_def]) >> simp[]) >>
  `0 <= i /\ Num i < bound_length bd /\
   (!n. bd = Dynamic n ==> Num i < w2n (lookup_storage slot (get_storage cx fin tr)))` by
    fs[Abbr `dyn`, AllCaseEqs()] >>
  `iw = n2w (Num i)` by
    (`i2w i = iw` by
       (Cases_on `is_signed_type (expr_type idx)` >- simp[integer_wordTheory.i2w_w2i] >>
        simp[integer_wordTheory.i2w_def]) >>
     qpat_x_assum `i = if _ then _ else _` kall_tac >>
     `~(i < 0)` by
       (qpat_assum `0 <= i` (fn th => ACCEPT_TAC (REWRITE_RULE [GSYM integerTheory.INT_NOT_LT] th))) >>
     qpat_x_assum `i2w i = iw` mp_tac >> simp[integer_wordTheory.i2w_def]) >>
  qabbrev_tac `off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv` >>
  `!tail. select_result cx (ArrayT et bd) (PlaceR (StoragePlace tr slot vt))
     (ValueSubscript key) (fin with gas_obs := tail) =
     (INL (PlaceR (StoragePlace tr (slot + n2w off) etv)), fin with gas_obs := tail)` by
    (`!tail. get_storage cx (fin with gas_obs := tail) tr = get_storage cx fin tr` by
       (Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     qpat_x_assum `vt = _` SUBST_ALL_TAC >>
     qpat_x_assum `key = _` SUBST_ALL_TAC >>
     qpat_x_assum `i = if _ then _ else _` kall_tac >>
     Cases_on `bd` >> gvs[Abbr `off`, vyperStateTheory.select_result_def,
                          extend_place_storage_array_index]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  conj_tac >- (
    qexistsl [`Gq`,`fin`,`INL (PlaceR (StoragePlace tr (slot + n2w off) etv))`,`q`,`tnq`] >>
    conj_tac >- metis_tac[] >>
    qx_gen_tac `H` >> strip_tac >>
    conj_tac >- metis_tac[] >>
    `fin with gas_obs := [] = fin` by simp[vyperStateTheory.evaluation_state_component_equality] >>
    simp[vyperASTTheory.expr_type_def] >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> storage_place_observed _ _ /\ _`
      (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
    `array_length_frame sn u Gi tni q Gq tnq` by simp[] >>
    fs[bodyFullTargetArrayLoadTheory.array_length_frame_def] >>
    `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
      (qpat_assum `((q with vs_inst_idx := _) with vs_vars := _) = u` mp_tac >>
       simp[venomStateTheory.venom_state_component_equality]) >>
    `q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas /\
     q.vs_alloca_next = u.vs_alloca_next` by
      (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
         (fn th => once_rewrite_tac [th]) >> simp[]) >>
    `local_ptrs_reserved cenv sn` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
    `stmt_state_rel H ctx func cenv cx fin u` by metis_tac[expr_post_state] >>
    `stmt_state_rel H ctx func cenv cx fin q` by
      (irule bodyPtrSignedConvertSourceFrameTheory.stmt_state_rel_readonly_vars_pc >>
       qexistsl [`u`,`sn`] >> simp[]) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
      (qpat_assum `stmt_state_rel H ctx func cenv cx fin q`
         (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
    `eval_operand dst q = SOME (slot + n2w off)` by
      (qpat_assum `eval_operand dst q = SOME _` mp_tac >>
       Cases_on `bd` >>
       simp[Abbr `dyn`, Abbr `off`, wordsTheory.word_mul_n2w,
            GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_0,
            AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
    `storage_place_observed H (StoragePlace tr (slot + n2w off) etv)` by
      (qpat_x_assum `storage_place_observed H (StoragePlace tr slot vt)` mp_tac >>
       PURE_REWRITE_TAC [vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
       disch_then (qx_choose_then `root` (qx_choose_then `rt` (qx_choose_then `path`
         (qx_choose_then `delta` (map_every assume_tac o CONJUNCTS))))) >>
       `storage_subregion (ArrayTV etv bd) [ValueSubscript (IntV i)] off etv` by
         (`off = (case bd of Fixed _ => 0 | Dynamic _ => 1) +
                 Num i * type_slot_size etv /\ 0 <= i /\ Num i < bound_length bd`
          suffices_by
            (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bd` >>
             simp[vyperStoragePlaceRegionTheory.storage_subregion_def,
                  vyperASTTheory.bound_length_def]) >> simp[Abbr `off`]) >>
       qexistsl [`root`,`rt`,`path ++ [ValueSubscript (IntV i)]`,`delta + off`] >>
       qpat_assum `slot = root + n2w delta` (fn th => simp[th, GSYM wordsTheory.word_add_n2w,
                                                       wordsTheory.WORD_ADD_ASSOC]) >>
       irule vyperStoragePlaceRegionTheory.storage_subregion_append >>
       qexists `ArrayTV etv bd` >> metis_tac[]) >>
    `expr_body_pre cenv cx env (Subscript et obj idx) (es with gas_obs := gs1)` by simp[] >>
    `expr_body_pre cenv cx env idx mid` by
      (drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
    `!l. iop <> Label l` by
      (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
    `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
      (qpat_assum `eval_expr cx obj _ = _`
         (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >>
       simp[]) >>
    `ci_mono sn sb` by
      (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ sn = _`
         (mp_tac o AP_TERM ``SND : (operand # compile_state) -> compile_state``) >>
       simp[NoAsms] >> disch_then (SUBST1_TAC o SYM) >>
       irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
       simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
    `sm.cs_next_id <= sb.cs_next_id` by fs[exprLoweringPropsTheory.ci_mono_def] >>
    `well_formed_type_value etv` by
      metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
    `bt = ArrayT et bd` by
      (qpat_assum `vv_post H _ _ _ _ obj _ _ _ _ _ _ _ _`
         (mp_tac o PURE_REWRITE_RULE [vv_post_def]) >>
       disch_then (map_every assume_tac o CONJUNCTS) >>
       qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
       simp[vv_holds_def, compileEnvTheory.is_bytestring_type_def]) >>
    `vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sb s0 fin
      (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) (LocatedValue (ArrayT et bd) p) q` by
      (irule live_storage_array_base_endpoint >> fs[] >> metis_tac[]) >>
    conj_tac >-
      (irule live_storage_array_element_post >> fs[] >>
       qexistsl [`bd`,`i`,`p`] >> simp[Abbr `off`, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
    `slot_loc tr <> LocMemory /\ slot_loc tr <> LocCode` by
      (Cases_on `tr` >> simp[slot_loc_def]) >>
    simp[exprSimMemDefsTheory.vv_store_bound_nonmem, vv_location_def,
         contextTheory.ptr_accessors, mk_ptr_def] >>
    `ghost_inv_at (DF H) lo d cenv cx fin Gq tnq q` by
      (`local_ptrs_rel func cenv fin.scopes u` by
         metis_tac[stmt_state_rel_local_ptrs_alloca] >>
       `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
         metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LE_TRANS] >>
       `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
         metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LE_TRANS] >>
       irule alloc_buffer_ghost_inv_at_locals >>
       (conj_tac >- metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
       qexistsl [`Gi`,`u.vs_alloca_next`,`func`,`u`,`sn`,`tni`] >>
       simp[ptrDisciplineTheory.op_taint_def] >>
       qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u` (fn th =>
         once_rewrite_tac [GSYM th]) >> simp[venomStateTheory.venom_state_component_equality]) >>
    `ptr_vv_ok cx et (PlaceR (StoragePlace tr (slot + n2w off) etv))
       (LocatedValue et (mk_ptr dst (slot_loc tr))) fin Gq tnq q` by
      (irule subscript_observed_slot_ptr_at >> simp[mk_ptr_def] >> metis_tac[]) >>
    `wb_frame cenv es mid sa s0 s` by
      (qpat_assum `vv_post H _ _ _ _ obj _ _ _ _ _ _ _ _` mp_tac >>
       simp[NoAsms, vv_post_def, wb_frame_def] >> metis_tac[]) >>
    `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
      (drule_all (wordArgsPtrTheory.ghost_kept_at_wb_trans |> horizonTypeLib.at_horizon_named "H") >> simp[]) >>
    simp[GSYM mk_ptr_def] >>
    `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >> simp[] >>
    irule ghost_kept_at_clean_suffix >>
    qexistsl [`Gi`,`tni`] >> simp[ptrDisciplineTheory.op_taint_def] >>
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LE_TRANS]) >> simp[]
QED
