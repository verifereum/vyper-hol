(* Install the selected local write after the two successful source cuts. *)
Theory bodyAssignLocalReachedMemoryOutcomeMods
Ancestors
  bodyAssignLocalReachedMemoryFrameMods bodyAssignLocalWriteInstallOutcomeMods
  bodyAssignLocalRawOperandAtStoreMods bodyAssignLocalSnapshotOperandAtStoreMods
  bodyAssignLocalEmptyInstallAtPathMods bodyAssignLocalWordInstallAtPathMods
  bodyAssignLocalBytesInstallAtPathMods bodyAssignLocalLayoutInstallAtPathMods
  bodyAssignLocalWidenInstallAtPathMods bodyPlaceWriteTailAdmissibleMods
  placeRelayoutOutcome tuplePlaceSourceGas fragGasOriginPtrLoop
  exprOpenTerminals placeRelayoutOpen wideningZeroLayout
  stmtLoweringMono exprLoweringProps fragExec compileEnv
  gasContext vyperState vyperPlaceFrames bodyAssignLocalStoreCutsMods
  bodyQualifiedPlaceTargetEntryMods bodyAssignQualifiedStageJoinMods
  bodyAssignLocalPreStoreMods bodyQualifiedPlaceRhsPostMods loweringStateRelDefs loweringPosts
Libs monadsyntax

val rhs_post =
  ``qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0``;

val here =
  ``local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw) ee``;

val normal =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef Gf tf t.
      ?ce. stmt_lands lctx sb res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
        immutable_frame_mods func ce cx ef t /\ storage_well_formed_on cx ef (FST H) /\
        return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ef t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ef t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
          off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem reached_local_write_result[local]:
  gas_admissible (write_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) ee /\
  ee.gas_obs = [] ==>
  ?ff. write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
       (!tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
           (INL (),ff with gas_obs := tail)) /\
       ff.storage_trace = ee.storage_trace /\ ff.gas_obs = []
Proof
  strip_tac >> Cases_on `write_place cx (MemoryPlace id path) v ee` >>
  rename1 `write_place _ _ _ _ = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (drule gas_admissible_result >>
     disch_then (qspecl_then [`res`,`[]`,`ff`] mp_tac) >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     simp[]) >>
  drule_all_then SUBST_ALL_TAC memory_write_admissible_success >>
  drule_then strip_assume_tac write_memory_place_frame >>
  simp[tuple_place_write_gas_obs]
QED

Theorem reached_local_install_result[local]:
  ~z.vs_halted /\
  (!tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
           (INL (),ff with gas_obs := tail)) /\
  ff.storage_trace = ee.storage_trace /\ ff.gas_obs = [] /\
  (?t Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (z,Gz,tz) [] (OK t,Gf,tf) /\
     local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
       (ff with gas_obs := []) t Gf tf s0 sa es G0 tn0 (INL ())) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz)
    ^normal X
Proof
  strip_tac >> irule assign_local_write_install_outcome_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ff`,`t`,`tf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  BETA_TAC >> qexists_tac `cenv` >> fs[local_assign_normal_at_cut_mods] >>
  first_assum ACCEPT_TAC
QED

Theorem assign_local_reached_memory_outcome_with_raw_mods:
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME (Type dty) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_widens_to env.type_defs (expr_type e) dty /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  (!vv entry p cap b off ptv dw ff.
     saved = SOME vv /\ ~expr_can_mutate cenv (target_to_expr bt) /\
     ^here st z Gz tz /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
     ?opd cur sw s G tn.
       unwrap_value cenv vv st = (opd,cur) /\
       compile_assign_value cenv (FST dst) LocMemory opd (is_word_type dty)
         (vv_location vv) dty (lowered_value_type cenv e)
         (type_memory_bytes cenv dty) cur = ((),sb) /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (z,Gz,tz) [] (OK s,G,tn)) /\
       ^here cur s G tn /\
       local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw)
         (opd,sw) sa ee cur s G tn) /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\ return_buf_sep d cenv es s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  (?entry old. lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL old) /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) /\
  ~block_is_terminated st ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz)
    ^normal
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `?entry p cap b off ptv dw. ^here st z Gz tz` by
    (irule assign_local_reached_memory_frame_mods >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `lookup_scopes id ee.scopes = SOME entry` kall_tac >>
  qpat_x_assum `evaluate_subscripts _ _ path = INL old` kall_tac >>
  rename1 `local_assign_here_mods _ _ _ _ _ _ _ (entry,p,cap,b,off,ptv,dw) ee st z Gz tz` >>
  drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  drule_all_then assume_tac assign_reached_write_admissible_mods >>
  drule_all_then strip_assume_tac reached_local_write_result >>
  irule reached_local_install_result >>
  conj_tac >- fs[local_assign_here_mods_def] >>
  qexists_tac `ff` >> simp[] >>
  qpat_assum `ff.storage_trace = ee.storage_trace` (pure_once_rewrite_tac o single o SYM) >>
  Cases_on `saved`
  >- (irule assign_local_empty_install_at_path_mods >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  rename1 `SOME vv` >> suspend "operand"
QED

Resume assign_local_reached_memory_outcome_with_raw_mods[operand]:
  `?opd cur sw s G tn.
      unwrap_value cenv vv st = (opd,cur) /\
      compile_assign_value cenv (FST dst) LocMemory opd (is_word_type dty)
        (vv_location vv) dty (lowered_value_type cenv e)
        (type_memory_bytes cenv dty) cur = ((),sb) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,Gz,tz) [] (OK s,G,tn)) /\
      ^here cur s G tn /\
      local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw)
        (opd,sw) sa ee cur s G tn` by
    (Cases_on `expr_can_mutate cenv (target_to_expr bt)`
     >- (drule_all assign_local_snapshot_operand_at_store_mods >>
         disch_then (qspecl_then [`shadow_ctx`,`PG`]
           (qx_choosel_then [`opd`,`cur`,`s`,`G`,`tn`,`sw`] strip_assume_tac)) >>
         qexistsl_tac [`opd`,`cur`,`sw`,`s`,`G`,`tn`] >> asm_rewrite_tac[]) >>
     qpat_assum `!vv entry p cap b off ptv dw ff. _` irule >>
     qpat_assum `local_assign_here_mods _ _ _ _ _ _ _ _ ee st z Gz tz`
       (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = (INL (),_)` (irule_at Any) >>
     simp[]) >>
  rename1 `unwrap_value cenv vv st = (opd,cur)` >>
  `fn_has_code cur sb func` by
    (`cs_extends st cur` by
       (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
     `cs_extends cur sb` by
       (`ci_mono cur (SND (compile_assign_value cenv (FST dst) LocMemory opd
          (is_word_type dty) (vv_location vv) dty (lowered_value_type cenv e)
          (type_memory_bytes cenv dty) cur))` by simp[ci_mono_stmt_helpers] >>
        pop_assum mp_tac >> simp[ci_mono_def]) >>
     qpat_assum `fn_has_code st sb func`
       (mp_then (Pat `fn_has_code _ _ _`) mp_tac fn_has_code_split) >>
     disch_then (qspec_then `cur` mp_tac) >> simp[]) >>
  `?t Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) [] (OK t,Gf,tf) /\
       local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
         (ff with gas_obs := []) t Gf tf s0 sa es G0 tn0 (INL ())` suffices_by
    (strip_tac >> qexistsl_tac [`t`,`Gf`,`tf`] >> gen_tac >> disch_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       (qpat_assum `ff.storage_trace = ee.storage_trace`
          (pure_once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H ff.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then assume_tac)) >>
     conj_tac >- (irule gas_origin_ptr_path_trans >> rpt (first_assum (irule_at Any))) >>
     first_assum ACCEPT_TAC) >>
  Cases_on `is_word_type dty`
  >- (pure_rewrite_tac[local_assign_normal_at_cut_mods] >>
      irule (BETA_RULE assign_local_word_install_at_path_mods) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- (irule assign_local_bytes_install_at_path_mods >>
      rpt (first_assum (irule_at Any)) >>
      qpat_assum `~is_word_type dty` (fn nw =>
        qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
          (ACCEPT_TAC o REWRITE_RULE [nw]))) >>
  Cases_on `dty = lowered_value_type cenv e \/ tuple_memory_layout_eq dty (lowered_value_type cenv e)`
  >- suspend "layout" >>
  suspend "widen"
QED

Resume assign_local_reached_memory_outcome_with_raw_mods[layout]:
  pure_rewrite_tac[local_assign_normal_at_cut_mods] >>
  irule (BETA_RULE assign_local_layout_install_at_path_mods) >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  `env.type_defs = get_tenv cx` by
    (drule_then assume_tac exprBodyPrePropsTheory.expr_body_pre_mods_inv >>
     drule_then assume_tac exprBodyPrePropsTheory.expr_sim_inv_mods_env >>
     drule_then ACCEPT_TAC vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv) >>
  `evaluate_type (get_tenv cx) dty = SOME ptv` by fs[local_assign_here_mods_def] >>
  qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
  simp[vyperTypeSystemTheory.type_stmt_def, vyperTypeSystemTheory.atarget_accepts_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all_then assume_tac vyperTypeArgFitsTheory.type_widens_to_assignable_type >>
  drule_all_then assume_tac vyperTypeSystemTheory.assignable_type_slot_size_pos >>
  drule_then assume_tac (CONJUNCT1 valueEncodingPropsTheory.type_memory_size_pos) >>
  strip_tac >> gvs[]
QED

Resume assign_local_reached_memory_outcome_with_raw_mods[widen]:
  qpat_assum `~is_word_type dty` (fn nw =>
    qpat_assum `local_assign_store_source_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SRULE [local_assign_store_source_mods_def,LET_THM,nw])) >>
  qpat_assum `local_assign_here_mods _ _ _ _ _ _ _ _ ee cur s G tn`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  `0 < type_memory_size stv` by
    (Cases_on `type_memory_size stv = 0` >-
       (drule_all_then assume_tac type_widens_to_zero_layout >> gvs[]) >> decide_tac) >>
  `0 < type_memory_size ptv` by
    (drule_then assume_tac exprBodyPrePropsTheory.expr_body_pre_mods_inv >>
     drule_then assume_tac exprBodyPrePropsTheory.expr_sim_inv_mods_env >>
     drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
     qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
     simp[vyperTypeSystemTheory.type_stmt_def, vyperTypeSystemTheory.atarget_accepts_def,
          AllCaseEqs()] >> strip_tac >> gvs[] >>
     drule_all_then assume_tac vyperTypeArgFitsTheory.type_widens_to_assignable_type >>
     drule_all_then assume_tac vyperTypeSystemTheory.assignable_type_slot_size_pos >>
     drule_then ACCEPT_TAC (CONJUNCT1 valueEncodingPropsTheory.type_memory_size_pos)) >>
  `n = type_memory_size stv` by
    (qpat_assum `~is_bytestring_type dty` (fn nb =>
       qpat_assum `if _ then _ else n = _` (ACCEPT_TAC o SRULE [nb]))) >>
  `0 < n` by simp[] >>
  qpat_assum `0 < n ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `0 < type_memory_size ptv ==> _` (drule_then strip_assume_tac) >>
  `expr_sim_inv_mods mods cenv cx env ee` by
    (drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (assume_tac o SRULE [listTheory.APPEND_NIL])) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th =>
       qpat_assum `eval_target_place _ _ _ = _` (assume_tac o REWRITE_RULE [th])) >>
     `expr_sim_inv_mods mods cenv cx env ee /\
      body_const_cells_agree_mods mods cx env ee` suffices_by simp[] >>
     irule bodyPlaceWriteSourceModsTheory.place_write_reached_source_mods >>
     qpat_assum `eval_target_place _ _ _ = (INL _,ee)` (irule_at Any) >> simp[]) >>
  `w2n dw + type_memory_size ptv <= s.vs_alloca_next` by decide_tac >>
  `w2n dw + type_memory_size ptv < dimword (:256)` by decide_tac >>
  `not_fresh_at cur p` by
    (qpat_assum `local_ptrs_reserved cenv cur`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 q sz1 sz2. FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var q) sz1) ==> _`
       (qspecl_then [`id`,`id`,`p`,`cap`,`cap`] mp_tac) >> simp[]) >>
  `vv_location vv = SOME LocMemory ==>
    expr_val_at cenv cx (lowered_value_type cenv e)
      (cur with cs_next_id := 0) cur ee v opd s` by
    (strip_tac >> qpat_assum `vv_location vv = SOME LocMemory /\ 0 < n ==> _`
       (drule_all_then strip_assume_tac)
     >- (simp[expr_val_at_def] >>
         qpat_x_assum `expr_val_at _ _ _ sa cur ee _ _ _`
           (mp_tac o REWRITE_RULE [expr_val_at_def]) >> simp[] >>
         disch_then (DISJ_CASES_THEN2 strip_assume_tac assume_tac)
         >- (disj1_tac >>
             qpat_assum `FLOOKUP s.vs_allocas _ = SOME (_,_)` (irule_at Any) >>
             rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
         simp[]) >>
     simp[expr_val_at_def] >> disj1_tac >>
     qexistsl_tac [`aid`,`w2n sw`,`n`] >>
     simp[exprSimPropsTheory.val_footprint_le] >>
     rpt strip_tac >>
     qpat_assum `!name b cap. local_region _ _ _ name b cap ==> regions_disjoint _ _ b cap`
       (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `compile_assign_value cenv (Var x') LocMemory (Var x) F (vv_location vv) dty
     (lowered_value_type cenv e) (type_memory_bytes cenv dty) cur = ((),sb)` by
    (qpat_assum `FST dst = Var x'` (fn hd =>
       qpat_assum `opd = Var x` (fn src =>
         qpat_assum `~is_word_type dty` (fn guard =>
           qpat_assum `compile_assign_value cenv (FST dst) LocMemory opd (is_word_type dty) _ _ _ _ cur = ((),sb)`
             (ACCEPT_TAC o REWRITE_RULE [hd,src,guard]))))) >>
  `lookup_var x s = SOME sw /\ lookup_var x' s = SOME dw` by
    (conj_tac
     >- (qpat_assum `opd = Var x` (fn eq =>
           qpat_assum `eval_operand opd s = _`
             (ACCEPT_TAC o REWRITE_RULE [eq,venomStateTheory.eval_operand_def]))) >>
     qpat_assum `FST dst = Var x'` (fn eq =>
       qpat_assum `eval_operand (FST dst) s = _`
         (ACCEPT_TAC o REWRITE_RULE [eq,venomStateTheory.eval_operand_def]))) >>
  `vv_location vv <> SOME LocMemory /\ 0 < type_memory_size stv ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size ptv <= w2n sw` by
    (strip_tac >>
     qpat_assum `~(dty = lowered_value_type cenv e \/ _)`
       (strip_assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
     qpat_x_assum `vv_location vv <> SOME LocMemory /\ ~is_bytestring_type dty /\ _ ==> _`
       mp_tac >> simp[]) >>
  `~block_is_terminated cur` suffices_by
    (strip_tac >> irule assign_local_widen_install_at_path_mods >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `compile_assign_value _ (Var _) _ (Var _) F _ _ _ _ _ = _`
       (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = (INL (),_)` (irule_at Any) >>
     qpat_assum `mem_path_offset _ _ = SOME (_,_)` (irule_at Any) >>
     qpat_assum `lookup_scopes id ee.scopes = SOME entry` (irule_at Any) >>
     qpat_assum `FLOOKUP cenv.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ ee` (irule_at Any) >>
     qexistsl_tac [`b`,`sw`,`stv`,`cur with cs_next_id := 0`,`dw`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
     rpt strip_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qmatch_goalsub_rename_tac `not_fresh_at cur y` >>
          qpat_assum `ret_pc_ok cenv cur s` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >>
          disch_then (qspecl_then [`y`,`sz`] mp_tac) >> simp[] >> NO_TAC) >>
     TRY (qpat_assum `valid_horizon cx st0 H ee.storage_trace` (K ALL_TAC) >>
          qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
            (qspec_then `H` mp_tac) >> simp[] >> NO_TAC) >>
     TRY (qpat_assum `opd = Var x` (fn eq =>
            qpat_assum `vv_location vv = SOME LocMemory ==> expr_val_at _ _ _ _ _ _ _ opd _`
              (mp_tac o REWRITE_RULE [eq])) >> simp[] >> NO_TAC) >>
     qpat_assum `n = type_memory_size stv` (fn eq =>
       qpat_assum `ptr_covers G tn x s n` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  irule unwrap_value_open >>
  qpat_assum `unwrap_value cenv vv st = (opd,cur)` (irule_at Any) >>
  first_assum ACCEPT_TAC
QED

Finalise assign_local_reached_memory_outcome_with_raw_mods

Theorem assign_local_reached_memory_outcome_mods:
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME (Type dty) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_widens_to env.type_defs (expr_type e) dty /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\ return_buf_sep d cenv es s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  (?entry old. lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL old) /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) /\
  ~block_is_terminated st ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz)
    ^normal
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> irule assign_local_reached_memory_outcome_with_raw_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  qhdtm_assum `type_stmt` (irule_at Any) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` (irule_at Any) >>
  qexistsl_tac [`old`,`exps`,`entry`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `saved = SOME _` SUBST_ALL_TAC >>
  irule assign_local_raw_operand_at_store_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tops`,`src`,`shadow_func`,`exps`] >> simp[]
QED
