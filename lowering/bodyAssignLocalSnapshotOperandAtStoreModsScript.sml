(* The mutating target is reached after the RHS has been saved. *)
Theory bodyAssignLocalSnapshotOperandAtStoreMods
Ancestors
  bodyAssignLocalPreStoreMods bodyAssignLocalSnapshotMods
  bodyQualifiedPlaceRhsPostMods bodyCopyReadPhysicalTypeMods
  bodyAssignQualifiedStageJoinMods bodyWriteTargetStageMods
  exprBodyPreProps exprWordOperand exprReasonOperand exprSimHypsDefs
  bodyFullTargetDefs typedMemoryCopy aggregateEvaluatedLayout
  stmtSimDeclStore valueEncodingTyping fragGasOriginPtr
  loweringPosts exprLoweringProps exprLowering venomState bodyPtrDefs
  ptrDiscipline vyperStorageFootprint finite_map words arithmetic
  compileEnv context vyperTypeInvariants vyperTypeEvalCaseProofs
  vyperTypeSystem vyperTypeArgFits typedCopyCompatibility logArgumentTypeEval
  bodyAssignLocalPlaceRoutesMods vyperStorageTrace freshWrites loweringStateRelDefs

Theorem local_snapshot_memory_size[local]:
  expr_sim_inv_mods mods cenv cx env es /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes cenv ty = type_memory_size tv
Proof
  strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem local_snapshot_word_operand[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  lowered_value_type cenv e = expr_type e /\ is_word_type (expr_type e) /\
  compile_expr cenv (expr_type e) e sa = (raw,sm) /\
  compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm =
    (StackValue (lowered_value_type cenv e) op,sr) ==>
  !l. op <> Label l
Proof
  strip_tac >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >> fs[expr_sim_inv_mods_def]) >>
  `vv_type raw = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `raw` >> gvs[reason_result_shape_def,vv_type_def]) >>
  `vv_with_type (expr_type e) raw = raw` by
    (Cases_on `raw` >> gvs[vv_type_def,vv_with_type_def]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,sr)` by
    (Cases_on `unwrap_value cenv raw sm` >>
     gvs[lower_value_def,compile_snapshot_vv_def,comp_bind_def,comp_return_def]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (drule expr_sim_inv_mods_env >> metis_tac[logArgumentTypeEvalTheory.consistent_variable_type_well_formed]) >>
  drule lower_value_word_shape >>
  disch_then (qspec_then `env` mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Theorem local_snapshot_word_at_target[local]:
  wb_frame cenv mid ee sr u z /\ ghost_kept_at lo cenv mid sr Gu tu u Gz tz /\
  (!x. op = Var x ==> not_fresh_at sr x) /\ (!l. op <> Label l) /\
  eval_operand op u = SOME w /\ op_taint tu op = {} ==>
  eval_operand op z = SOME w /\ op_taint tz op = {}
Proof
  Cases_on `op` >> simp[eval_operand_def]
  >- simp[op_taint_def] >>
  strip_tac >> fs[wb_frame_def,ghost_kept_at_def] >>
  rename1 `not_fresh_at sr x` >>
  qpat_assum `!x. not_fresh_at sr x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED

Theorem local_snapshot_memory_target_post[local]:
  write_target_post_mods H D lo d ctx func ce cx bt mid sr st u ee
    (PlaceR (MemoryPlace id path)) (Type dty) dst Gu tu Gz tz z ==>
  assign_target_post F H ctx func ce cx mid sr st u ee (MemoryPlace id path) dty dst Gz z
Proof
  simp[assign_target_post_def,target_post_def,write_target_post_mods_def,
       write_target_location_mods_def,wb_frame_def,SF CONJ_ss] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

val here = ``local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
  (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw) ee``;

val source = ``local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST (dst : operand # data_location option # place_ty option),dw)``;

Theorem assign_local_snapshot_operand_at_store_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv) sr st
    shadow_sr shadow_st dst /\
  expr_can_mutate cenv (target_to_expr bt) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0 H v mid Gu tu u) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
     (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
      ee (PlaceR (MemoryPlace id path)) (Type dty) dst Gu tu Gz tz z) /\
  ^here st z Gz tz /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?op cur s G tn sw.
    unwrap_value cenv vv st = (op,cur) /\
    compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
      (vv_location vv) dty (lowered_value_type cenv e) (type_memory_bytes cenv dty) cur = ((),sb) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,Gz,tz) [] (OK s,G,tn)) /\
    ^here cur s G tn /\ ^source (op,sw) sa ee cur s G tn
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    (`valid_horizon cx st0 H0 (mid with gas_obs := target_gas).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [``:'a`` |-> ``:place``] valid_horizon_frame) >>
     qexistsl_tac [`eval_target_place cx bt`,`INL (MemoryPlace id path)`,
                  `ee with gas_obs := []`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (assume_tac o SRULE [listTheory.APPEND_NIL])) >>
     simp[evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  qpat_assum `expr_can_mutate cenv (target_to_expr bt)` (fn mut =>
    qhdtm_assum `qualified_place_rhs_post_mods`
      (strip_assume_tac o CONJUNCT2 o SRULE [mut] o
       MATCH_MP qualified_place_rhs_saved_view_mods)) >>
  `stmt_state_rel H0 ctx func cenv cx mid u /\ local_ptrs_reserved cenv sr` by
    (qhdtm_assum `qualified_place_rhs_post_mods`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE [qualified_place_rhs_post_mods_def]) >> simp[]) >>
  pop_assum strip_assume_tac >>
  qhdtm_x_assum `qualified_place_rhs_post_mods` kall_tac >>
  qhdtm_x_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
   evaluate_type (get_tenv cx) dty = SOME ptv /\ eval_operand (FST dst) z = SOME dw` by
    (qhdtm_assum `local_assign_here_mods`
       (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `env_consistent env cx es` by drule_then ACCEPT_TAC expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_formed_type env.type_defs (expr_type e)` by
    drule_all_then ACCEPT_TAC checked_expr_type_well_formed >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl_tac [`cx`,`env`,`es`,`mods`] >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[type_widens_to_def]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    (irule typedCopyCompatibilityTheory.type_widens_to_trans >> qexists_tac `expr_type e` >> simp[]) >>
  `value_has_type ptv v` by (drule_all type_widens_to_value_has_type >> simp[]) >>
  `?op sw. unwrap_value cenv vv st = (op,st) /\
      ^source (op,sw) sa ee st z Gz tz` suffices_by
    (strip_tac >> qexistsl_tac [`op`,`st`,`z`,`Gz`,`tz`,`sw`] >>
     simp[gas_origin_ptr_path_rules] >>
     qpat_assum `dst = (FST dst,_,_)` (fn shape =>
       qpat_assum `assign_place_store_code_mods cenv e (SOME vv) dst st = _`
         (mp_tac o ONCE_REWRITE_RULE [shape])) >>
     simp[assign_place_memory_store_code_mods,comp_bind_def]) >>
  `is_word_type (lowered_value_type cenv e) <=> is_word_type dty` by
    (qpat_assum `type_widens_to _ (lowered_value_type cenv e) dty` mp_tac >>
     simp[NoAsms,type_widens_to_def] >> strip_tac >>
     simp[arg_type_fits_word_type]) >>
  Cases_on `is_word_type dty`
  >- (`is_word_type (lowered_value_type cenv e)` by simp[] >>
      qpat_assum `is_word_type (lowered_value_type cenv e)` (fn word =>
        qpat_x_assum `if is_word_type (lowered_value_type cenv e) then _ else _`
          (qx_choose_then `op` strip_assume_tac o SRULE [word])) >>
      `lowered_value_type cenv e = dty /\ expr_type e = dty` by
        (conj_tac >> irule compileEnvTheory.type_widens_to_word >>
         simp[] >> qexists_tac `get_tenv cx` >> first_assum ACCEPT_TAC) >>
      `lowered_value_type cenv e = expr_type e /\ is_word_type (expr_type e)` by simp[] >>
      `!l. op <> Label l` by
        (qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
         drule_all_then ACCEPT_TAC local_snapshot_word_operand) >>
      `op_taint tu op = {}` by fs[ptr_val_ok_def] >>
      drule_all_then strip_assume_tac local_snapshot_word_at_target >>
      `post_value_type cenv e = dty` by simp[post_value_type_lowered] >>
      `store_lays_out ptv ptv v` by
        (qspecl_then [`get_tenv cx`,`dty`,`ptv`,`v`] mp_tac store_lays_out_typed >> simp[]) >>
      `tv = ptv` by
        (qpat_assum `lowered_value_type cenv e = dty` (fn eq =>
           qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME tv`
             (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
      qexistsl_tac [`op`,`typed_val_to_w256 ptv v`] >>
      simp[local_assign_store_source_mods_def,unwrap_value_def,comp_return_def]) >>
  `~is_word_type (lowered_value_type cenv e)` by simp[] >>
  qpat_assum `~is_word_type (lowered_value_type cenv e)` (fn nonword =>
    qpat_x_assum `if is_word_type (lowered_value_type cenv e) then _ else _`
      (qx_choose_then `x` (qx_choose_then `aid` (qx_choose_then `bs` strip_assume_tac))
        o SRULE [nonword])) >>
  `MAP FDOM ee.scopes = MAP FDOM mid.scopes` by fs[wb_frame_def,locals_kept_def] >>
  drule_then assume_tac local_snapshot_memory_target_post >>
  `~is_word_type (vv_type (vv_with_type (lowered_value_type cenv e) raw))` by
    (Cases_on `raw` >> simp[vv_type_def,vv_with_type_def]) >>
  `vv_operand vv = Var x` by simp[vv_operand_def,mk_ptr_def] >>
  `unwrap_value cenv vv st = (Var x,st)` by simp[unwrap_value_def,mk_ptr_def,comp_return_def] >>
  drule_all_then strip_assume_tac assign_local_snapshot_ready_mods >>
  `op_taint tz (Var x) = {}` by fs[ptr_covers_def] >>
  `bs < dimword (:256)` by decide_tac >>
  `w2n (n2w bs : 256 word) = bs` by simp[w2n_n2w,LESS_MOD] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
    drule_all_then ACCEPT_TAC local_snapshot_memory_size >>
  `type_memory_bytes cenv dty = type_memory_size ptv` by
    drule_all_then ACCEPT_TAC local_snapshot_memory_size >>
  qexistsl_tac [`Var x`,`n2w bs`] >>
  simp[local_assign_store_source_mods_def,eval_operand_def,value_has_type_val_wf] >>
  strip_tac >> disj2_tac >> qexists_tac `aid` >> simp[] >> first_assum ACCEPT_TAC
QED
