Theory bodyPopReachedSlotArmMods
Ancestors
  bodyPopInputsMods bodyPopReachedSlotMods bodyPopExitPathsMods bodyPopSlotRunMods
  bodyPopSlotPostMods gasOutcomeFullPostMods exprSimPopNestedBase
  exprBodyPreProps bodyWriteTargetStageMods vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomExecSemantics venomInst venomState
  stateRelProj accountsRelProps loweringStateRelDefs bodyFullShadowBodyInv
  loweringPosts bodyPtrDefs vyperTypeValues
  stmtReasonLitFragMemory freshWrites exprSimDefs haltExitProj vyperStorageBackend
  fragExec vyperStorage context list rich_list words

Theorem reached_slot_pop_shape[local]:
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (dst,sm) /\
  FST (SND dst) = SOME (slot_loc tr) /\
  SND (SND dst) = SOME (value_type_place (Type (ArrayT ann (Dynamic cap)))) /\
  word_scale (slot_loc tr) = 1 /\
  elem_size_in_location cenv (slot_loc tr) ann = type_slot_size tv ==>
  ?x0 x1 x2 x3 x4 x5 x6.
    ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
    EVERY (\x. ~not_fresh_at sm x) [x0;x1;x2;x3;x4;x5;x6] /\
    vv = LocatedValue ann (mk_ptr (Var x6) (slot_loc tr)) /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++
      nested_pop_suffix (FST dst) tr sm.cs_next_id (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6
Proof
  PairCases_on `dst` >> simp_tac std_ss [] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [nested_pop_compile_eq]) >>
  simp[LET_THM, exprLoweringTheory.value_type_place_def] >>
  Cases_on `compile_dynarray_pop dst0 1 (type_slot_size tv) cenv.ce_is_ctor
     cenv.ce_imm_alloca (slot_loc tr) sm` >> simp[] >> strip_tac >>
  qpat_assum `compile_dynarray_pop _ _ _ _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP nested_pop_suffix_shape o REWRITE_RULE [slot_loc_def]) >>
  qexistsl_tac [`x0`,`x1`,`x2`,`x3`,`x4`,`x5`,`x6`] >> gvs[]
QED

val pop_static_certificate =
  ``!hdr s slot tn tr n x0 x1 x2 x3 func lo ctx bb id explicit PG G.
    eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
    key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
    (if tr then tload slot s else sload slot s) = n /\ n <> 0w /\
    ALL_DISTINCT [x0;x1;x2;x3] /\
    EVERY (\x. hdr <> Var x) [x0;x1;x2;x3] /\
    s.vs_call_ctx.cc_static /\ alloca_history func s /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2];
      mk_inst (id+3) ASSERT [Var x2] [];
      mk_inst (id+4) SUB [Var x0;Lit 1w] [x3];
      mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?v G' tn'.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort ExHalt_abort v,G',tn')) /\
      v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = s.vs_inst_idx+5 /\
      allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
      v.vs_call_ctx.cc_static``;

Theorem pop_reached_slot_arm_mods:
  ^pop_static_certificate /\
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sm sb func /\
  gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0 /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (StoragePlace tr slot vt),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0 ee
      (PlaceR (StoragePlace tr slot vt)) (Type (ArrayT ann (Dynamic cap))) dst G0 tn0 G tn t) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (pop_place cx (StoragePlace tr slot vt)) (ee,t,G,tn)
    (\H res ef G' tn' u. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef tv vv u /\
      vv_store_bound cx (post_value_type cenv (Pop ann bt))
        (lowered_value_type cenv (Pop ann bt)) ef tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
      ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) tv vv ef G' tn' u /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Pop ann bt)) /\
           ~is_bytestring_type (post_value_type cenv (Pop ann bt)) ==>
           vv_own cenv cx (post_value_type cenv (Pop ann bt)) sa sb ef tv vv u /\
           (!t' ptr. vv = LocatedValue t' ptr ==> ptr.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ef = (INL v,ef) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Pop ann bt)) = SOME rt /\
                  eval_operand (vv_operand vv) u = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Pop ann bt)) ==>
                ptr_buf_ok cenv (Pop ann bt) op G' u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
                ptr_buf_ok cenv (Pop ann bt) ptr.ptr_operand G' u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "static_cert")
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_then strip_assume_tac pop_target_inputs_mods >>
  qhdtm_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `eval_target_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (StoragePlace tr slot vt),ee)` by
    (`ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     pop_assum mp_tac >> pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
     disch_then ACCEPT_TAC) >>
  drule_all_then strip_assume_tac pop_reached_slot_header_mods >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> MEM _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac reached_slot_pop_shape >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> simp[call_ctx_rel_def]) >>
  qpat_x_assum `vt = ArrayTV _ _` SUBST_ALL_TAC >>
  qabbrev_tac `hdr = FST dst` >>
  qabbrev_tac `id = sm.cs_next_id` >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. hdr = Var x ==> not_fresh_at sm x`
       (drule_then assume_tac) >>
     qpat_assum `EVERY _ [x0;x1;x2;x3;x4;x5;x6]`
       (qspec_then `x` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[]) >>
  Q.ASM_CASES_TAC `lookup_storage slot (get_storage cx ee tr) = 0w`
  >- suspend "empty" >>
  Q.ASM_CASES_TAC `cx.txn.is_static` >- suspend "static" >>
  suspend "writable"
QED

Resume pop_reached_slot_arm_mods[empty]:
  `isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1]; mk_inst (id+2) ISZERO [Var x1] [x2]]
      (DROP t.vs_inst_idx bb.bb_instructions)` by
    (irule listTheory.isPREFIX_TRANS >>
     qexists `nested_pop_suffix hdr tr id (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6` >>
     conj_tac
     >- (pure_rewrite_tac[nested_pop_suffix_def] >> simp[]) >>
     pure_asm_rewrite_tac[]) >>
  `get_instruction bb (t.vs_inst_idx+3) = SOME (mk_inst (id+3) ASSERT [Var x2] [])` by
    (drule_all_then strip_assume_tac fn_has_code_same_block >>
     qpat_assum `!i. i < LENGTH _ ==> get_instruction _ _ = _`
       (qspec_then `3` mp_tac) >> fs[Abbr `hdr`, Abbr `id`, nested_pop_suffix_def]) >>
  `(if tr then tload slot t else sload slot t) = 0w` by simp[] >>
  `ALL_DISTINCT [x0;x1;x2]` by
    (qpat_assum `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` mp_tac >> simp[NoAsms]) >>
  drule_all pop_slot_empty_exit_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`v`,`Gf`,`tf`] strip_assume_tac)) >>
  `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) ee =
      (INR (Error (RuntimeError "pop empty storage array")),ee)` by
    (qpat_assum `lookup_storage slot (get_storage cx ee tr) = 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     simp[pop_place_def, get_storage_backend_eq, bind_def,
          ignore_bind_def, check_def, assert_def, return_def, raise_def]) >>
  drule_then assume_tac nested_pop_storage_gas_obs >>
  irule gas_outcome_full_mods_exit_revert >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ee`,`INR (Error (RuntimeError "pop empty storage array"))`,`tf`,`v`] >>
  simp[exit_result_def, expr_exit_def, halt_exit_not_halt]
QED

Resume pop_reached_slot_arm_mods[static]:
  `isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1]; mk_inst (id+2) ISZERO [Var x1] [x2];
      mk_inst (id+3) ASSERT [Var x2] [];
      mk_inst (id+4) SUB [Var x0;Lit 1w] [x3];
      mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
      (DROP t.vs_inst_idx bb.bb_instructions)` by
    (irule listTheory.isPREFIX_TRANS >>
     qexists `nested_pop_suffix hdr tr id (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6` >>
     conj_tac >- simp[nested_pop_suffix_def] >> pure_asm_rewrite_tac[]) >>
  `ALL_DISTINCT [x0;x1;x2;x3]` by
    (qpat_assum `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` mp_tac >> simp[NoAsms]) >>
  `EVERY (\x. hdr <> Var x) [x0;x1;x2;x3]` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `x` >> rpt strip_tac >>
     qpat_assum `!x. hdr = Var x ==> ~MEM x _` (drule_then mp_tac) >>
     qpat_assum `MEM x [x0;x1;x2;x3]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `t.vs_call_ctx.cc_static` by simp[] >>
  asm_x "static_cert" drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`v`,`Gf`,`tf`] strip_assume_tac)) >>
  `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) ee =
     (INR (Error (RuntimeError "write in static context")),ee)` by
    (qpat_assum `lookup_storage slot (get_storage cx ee tr) <> 0w` mp_tac >>
     qpat_assum `cx.txn.is_static` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     `0 < w2n (lookup_storage slot (get_storage cx ee tr))` by
       (Cases_on `lookup_storage slot (get_storage cx ee tr)` >> fs[]) >>
     simp[pop_place_def, get_storage_backend_eq, write_storage_slot_def,
          check_not_static_def, bind_def, ignore_bind_def, check_def, assert_def,
          return_def, raise_def]) >>
  drule_then assume_tac nested_pop_storage_gas_obs >>
  irule gas_outcome_full_mods_exit_static >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ee`,`INR (Error (RuntimeError "write in static context"))`,`tf`,`v`] >>
  simp[expr_exit_def, halt_exit_not_halt]
QED

Resume pop_reached_slot_arm_mods[writable]:
  asm_x "static_cert" kall_tac >>
  `~t.vs_call_ctx.cc_static` by simp[] >>
  `isPREFIX (nested_pop_suffix hdr tr id (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6)
     (DROP t.vs_inst_idx bb.bb_instructions)` by pure_asm_rewrite_tac[] >>
  drule_all pop_slot_positive_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`raw`,`Gf`,`tf`] strip_assume_tac)) >>
  qabbrev_tac `u = raw with vs_inst_idx := t.vs_inst_idx+9` >>
  `u = raw with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (simp_tac std_ss [Abbr `u`] >>
     qpat_assum `sb.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     simp[nested_pop_suffix_def]) >>
  `u.vs_current_bb = sb.cs_current_bb /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (conj_tac
     >- (simp_tac std_ss [Abbr `u`] >>
         qpat_assum `raw = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
         Cases_on `tr` >> simp[sstore_def,tstore_def]) >>
     simp[Abbr `u`,exprPtrUnwrapFramesTheory.copy_allocas_inst_idx]) >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx ee tr))` >>
  `len = w2n (lookup_storage slot (get_storage cx ee tr)) /\ 0 < len /\ len <= cap` by
    (simp_tac (srw_ss()) [Abbr `len`, GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
      w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
      slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV tv (Dynamic cap)) /\
      storage_range_agree (get_storage cx ee tr)
        (if tr then contract_transient t else contract_storage t) slot (ArrayTV tv (Dynamic cap))` by
    (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `well_formed_type_value (ArrayTV tv (Dynamic cap))` by
    (simp[vyperTypingTheory.well_formed_type_value_def] >>
     drule_then ACCEPT_TAC evaluate_type_well_formed_type_value) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> qexists `sa` >> conj_tac
        >- (qpat_assum `ci_mono sa sm` (mp_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
            strip_tac >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     `~MEM x [x0;x1;x2;x3;x4;x5;x6]` by
       (qpat_assum `EVERY _ [x0;x1;x2;x3;x4;x5;x6]`
          (qspec_then `x` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        simp[]) >>
     qpat_assum `!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x raw = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     simp_tac (srw_ss()) [Abbr `u`, lookup_var_def] >>
     rpt conj_tac >> first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [lookup_var_def])) >>
  `tf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
   tf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans)` by
    (qpat_assum `if tr then tf.t_trans = _ /\ _ else _` mp_tac >>
     Cases_on `tr` >> simp_tac std_ss []) >>
  `raw = (if tr then tstore slot (tload slot t - 1w) t
          else sstore slot (sload slot t - 1w) t) with vs_vars := raw.vs_vars /\
   lookup_var x6 raw = SOME (slot + 1w +
     ((if tr then tload slot t else sload slot t) - 1w) * n2w (type_slot_size tv))` by
    (qpat_assum `raw = _ with vs_vars := _` mp_tac >>
     qpat_assum `lookup_var x6 raw = _` mp_tac >>
     qpat_assum `(if tr then tload slot t else sload slot t) = _`
       (mp_tac o GSYM) >>
     Cases_on `tr` >> simp_tac std_ss [] >>
     disch_then (fn th => simp_tac std_ss [th])) >>
  drule_all pop_slot_positive_post_mods >> simp_tac std_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ef = set_storage cx ee tr (apply_writes slot [(0,n2w (len - 1))]
    (get_storage cx ee tr))` >>
  qabbrev_tac `result = PlaceR (StoragePlace tr (slot + n2w (1 + (len - 1) * type_slot_size tv)) tv)` >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ef`,`INL result`,`u`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` (irule o SPEC_ALL)) >>
  `ef with gas_obs := [] = ef` by simp[evaluation_state_component_equality] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> qexists `result` >>
  qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==>
      vv_post_mods H ctx func cenv cx _ es sa sb s0 ef result _ u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `vv = LocatedValue _ _` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `ef with gas_obs := [] = ef` (fn th => pure_rewrite_tac [th]) >>
  simp_tac bool_ss [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `tr` >> simp_tac (srw_ss()) [Abbr `result`,vv_location_def,slot_loc_def,mk_ptr_def]
QED

Finalise pop_reached_slot_arm_mods
