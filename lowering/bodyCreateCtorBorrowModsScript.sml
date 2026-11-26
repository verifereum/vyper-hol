(* Linked borrowed aggregate constructor-head cut. *)
Theory bodyCreateCtorBorrowMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullCreateHeld
  bodyFullShadowBodyInv exprBodyPreProps exprSimHypsDefs exprSimMemorySource exprSimDefs stmtSimProps haltExitProj
  bodyInvCodeProps createSizeRawGasAdmissibleMods
  gasOutcomeFullMods gasOutcomeFull gasShadow gasContext
  bodyQualifiedSnapshotReadMods bodySavedRhsSlotLiveMods bodyCopyReadPhysicalTypeMods
  bodyForcedStorageFrameMods fragGasOriginPtr loweringPosts bodyMemoryDefs
  targetPureSourceFrame vyperEvalExprPreservesScopesDom
  createCtorSnapshotByteRetagMods exprPtrUnwrapStorageShape valueTypingMemoryProps
  bodyPtrDefs exprSimMemDefs context
  vyperInterpreter vyperStorageTrace vyperState vyperAST vyperTypeSystem vyperTypeCallGraph
  compileEnv exprLowering allocaHistory list pair option arithmetic
Libs monadsyntax

Theorem create_ctor_borrowed_head_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  body_expr_full_ok_mods mods exps cx e /\
  shadow_body_inv tops ctx shadow_ctx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sh = (vv,shb) /\
  compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) sb = (sv,sb) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) /\
  ~is_word_type (lowered_value_type cenv e) /\
  (!gs pv ee tag p. eval_expr cx e (es with gas_obs := gs) = (INL pv,ee) /\
     vv = LocatedValue tag p /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
       tag = expr_type e /\ (!v. pv <> Value v)) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code sh shb shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  immutable_frame_mods func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op. sv = StackValue tag op) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
          p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
          p.ptr_location <> LocMemory /\
          lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
         ptr_buf_ok cenv e (vv_operand sv) G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) /\
      immutable_frame_mods func cenv cx ee t /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
       (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
       (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
      _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_then assume_tac create_raw_gas_admissible_mods >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  qpat_assum `cenv.ce_modules = mods`
    (fn eq => qhdtm_x_assum `gas_outcome_full_mods`
      (assume_tac o REWRITE_RULE [eq])) >>
  irule qualified_snapshot_read_lift_mods >>
  qexistsl_tac [`cenv`,`d`,`sa`,`sb`,`vv`] >> BETA_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "read"
QED

Resume create_ctor_borrowed_head_mods[read]:
  qx_genl_tac [`marks`,`tv`,`v`,`ee`,`G1`,`tn1`,`t`] >> strip_tac >>
  qexistsl_tac [`t`,`G1`,`tn1`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` kall_tac >>
  suspend "endpoint"
QED

Resume create_ctor_borrowed_head_mods[endpoint]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by simp[bind_def] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then assume_tac saved_rhs_slot_live_mods >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `~expr_has_effect e ==>
    (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
    (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)` by
    (strip_tac >> drule_all effect_free_source_projection >> simp[]) >>
  qhdtm_x_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `wb_frame cenv es ee sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sb t` by
    (qpat_assum `compile_expr cenv _ e sa = _`
       (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `sv = ext_call_arg_value (lowered_value_type cenv e) vv` by
    fs[compile_snapshot_vv_def,comp_return_def] >>
  qpat_x_assum `sv = _` SUBST_ALL_TAC >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac copy_lowered_fits_mods >>
  `~is_word_type (expr_type e)` by (drule aggregateEvaluatedLayoutTheory.arg_type_fits_word_type >> simp[]) >>
  drule_all_then
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))
    copy_read_physical_type_gas_obs_mods >>
  qexists_tac `v` >> asm_rewrite_tac[] >> simp[NoAsms] >>
  suspend "representation"
QED

Resume create_ctor_borrowed_head_mods[representation]:
  `!tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory ==>
     lowered_value_type cenv e = expr_type e /\
     post_value_type cenv e = expr_type e /\ tag = expr_type e` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
     `tag = post_value_type cenv e` by
       (qpat_assum `vv_holds_mods _ _ _ _ (LocatedValue _ _) _ _` mp_tac >>
        Cases_on `p.ptr_location = LocCode`
        >- (qpat_assum `p.ptr_location = LocCode` (fn th => simp[NoAsms,th,vv_holds_mods_def])) >>
        qpat_assum `p.ptr_location <> LocCode` (fn th =>
          qpat_assum `p.ptr_location <> LocMemory` (fn th' =>
            simp[NoAsms,th,th',vv_holds_mods_def,vv_holds_def]))) >>
     `lowered_value_type cenv e = expr_type e` by
       (irule compile_nonmemory_lowered_value_type >>
        goal_assum (drule_at (Pat `compile_expr cenv _ e sa = _`)) >> simp[]) >>
     `post_value_type cenv e = expr_type e` by (drule_then ACCEPT_TAC post_value_type_lowered) >>
     simp[]) >>
  conj_tac
  >- (namedCases_on `vv` ["tag op","tag p"]
      >- simp[NoAsms,ext_call_arg_value_def] >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qpat_assum `p.ptr_location = LocMemory` (fn th => simp[NoAsms,ext_call_arg_value_def,th])) >>
      qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,ext_call_arg_value_def,th]) >>
      strip_tac >> qpat_assum `tag = _` SUBST1_TAC >>
      qpat_assum `lowered_value_type _ _ = _` (fn th => simp[NoAsms,th])) >>
  conj_tac >- suspend "retag" >>
  suspend "read_frame"
QED

Resume create_ctor_borrowed_head_mods[retag]:
  Cases_on `post_value_type cenv e = lowered_value_type cenv e`
  >- (qexists_tac `tv` >>
      qpat_assum `post_value_type _ _ = _` (fn eq =>
        map_every (fn pat => qpat_assum pat (mp_tac o REWRITE_RULE [eq]))
          [`vv_holds_mods _ _ _ _ vv _ _`, `vv_at _ _ _ _ _ _ _ vv _`,
           `ptr_vv_ok _ _ _ vv _ _ _ _`, `vv_store_bound _ _ _ _ _ vv _`,
           `read_result cx tv ee = _`]) >>
      namedCases_on `vv` ["tag op","tag p"] >- simp[NoAsms,ext_call_arg_value_def] >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qpat_assum `p.ptr_location = LocMemory` (fn th =>
          simp[NoAsms,th,ext_call_arg_value_def,vv_holds_mods_def,vv_holds_def,
               vv_at_def,ptr_vv_ok_def,vv_store_bound_def])) >>
      qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _` (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,th,ext_call_arg_value_def]) >>
      strip_tac >>
      qpat_assum `tag = expr_type e` SUBST_ALL_TAC >>
      qpat_assum `lowered_value_type cenv e = expr_type e` (fn th => simp[NoAsms,th])) >>
  qexists_tac `Value v` >>
  conj_tac >- simp[NoAsms,read_result_def,return_def] >>
  irule ctor_snapshot_bytes_retag_mods >>
  `is_bytestring_type (post_value_type cenv e) /\ is_bytestring_type (lowered_value_type cenv e)` by
    (qpat_assum `_ \/ is_bytestring_type _ /\ is_bytestring_type _` mp_tac >>
     qpat_assum `post_value_type cenv e <> lowered_value_type cenv e` (fn th => simp[NoAsms,th])) >>
  `val_wf rt v` by (drule_then ACCEPT_TAC value_has_type_memory_wf) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (namedCases_on `vv` ["tag op","tag p"] >- simp[NoAsms] >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qpat_assum `p.ptr_location = LocMemory` (fn th => simp[NoAsms,th])) >>
      qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,th]) >>
      rpt strip_tac >> qpat_assum `post_value_type cenv e <> lowered_value_type cenv e` mp_tac >>
      qpat_assum `post_value_type cenv e = expr_type e` (fn a =>
        qpat_assum `lowered_value_type cenv e = expr_type e` (fn b => simp[NoAsms,a,b])))
  >- (qexists_tac `rt` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`pt`,`tv`,`post_value_type cenv e`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_ctor_borrowed_head_mods[read_frame]:
  rpt conj_tac
  >- (namedCases_on `vv` ["tag op","tag p"]
      >- simp[NoAsms,ext_call_arg_value_def,vv_storage_live_def] >>
      Cases_on `p.ptr_location = LocMemory`
      >- (qpat_assum `p.ptr_location = LocMemory` (fn th =>
            simp[NoAsms,th,ext_call_arg_value_def,vv_storage_live_def])) >>
      qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,th]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `tag = expr_type e` SUBST_ALL_TAC >>
      qpat_assum `lowered_value_type cenv e = expr_type e` (fn th =>
        simp[NoAsms,th,ext_call_arg_value_def]) >>
      qpat_assum `vv_storage_live H cx (LocatedValue _ _) ee t`
        (ACCEPT_TAC o REWRITE_RULE [vv_storage_live_def]))
  >- (namedCases_on `vv` ["tag op","tag p"]
      >- (simp[NoAsms,ext_call_arg_value_def,vv_operand_def] >>
          qpat_assum `!tag op. _ ==> ptr_buf_ok _ _ op _ _`
            (qspecl_then [`tag`,`op`] mp_tac) >>
          qpat_assum `~is_word_type (post_value_type cenv e)` (fn th => simp[NoAsms,th])) >>
      qpat_assum `!tag p. _ ==> ptr_buf_ok _ _ p.ptr_operand _ _`
        (qspecl_then [`tag`,`p`] mp_tac) >>
      simp[NoAsms,ext_call_arg_value_def,vv_operand_def])
  >- suspend "code_read" >>
  strip_tac >>
  qpat_assum `~expr_has_effect e ==> _ = _` (drule_then mp_tac) >>
  simp[evaluation_state_component_equality]
QED

Resume create_ctor_borrowed_head_mods[code_read]:
  namedCases_on `vv` ["tag op","tag p"]
  >- simp[NoAsms,ext_call_arg_value_def,vv_location_def] >>
  simp[NoAsms,ext_call_arg_value_def,vv_location_def,vv_operand_def] >>
  strip_tac >>
  `p.ptr_location <> LocMemory` by simp[] >>
  qpat_assum `!tag p. LocatedValue _ _ = _ /\ _ ==> _`
    (qspecl_then [`tag`,`p`] mp_tac) >>
  qpat_assum `p.ptr_location <> LocMemory` (fn th => simp[NoAsms,th]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `cenv.ce_is_ctor /\ vv_location _ = SOME LocCode ==> _` mp_tac >>
  (impl_tac >- simp[vv_location_def]) >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn a =>
    qpat_assum `lowered_value_type cenv e = expr_type e` (fn b =>
      qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME rt` (fn ev =>
        qpat_assum `read_result cx tv ee = (INL v,ee)` (fn rd =>
          simp[NoAsms,a,GSYM b,ev,rd,vv_operand_def,arithmeticTheory.ADD_COMM]))))
QED

Finalise create_ctor_borrowed_head_mods
