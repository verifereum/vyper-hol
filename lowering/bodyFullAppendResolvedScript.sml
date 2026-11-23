(* Robust reconstruction of a memory array after appending one word. *)
Theory bodyFullAppendResolved
Ancestors
  stateRelProj stmtSimDefs vyperScopePreservation
  bodyFullPreds bodyFullSimProjection bodySimFull gasOutcomeFullCompose
  bodyFullShared bodyFullMemoryFrames bodyAppendResolvedPre appendMemoryRel appendMemoryPtr
  bodyNameMemoryFacts representationCleanPtr appendMemoryPath
  normalizationPrefixPtr robustCopyTransportPtr exprSimAggregateEncoding allocaHistoryFragment
  exprSimHypsDefs exprSimDefs exprSimSource exprSimProps loweringPosts
  exprLowering exprLoweringProps emitHelperProps compileEnv stmtSimAppendResolved
  gasShadowCompileStmtHelpers abiBuiltinEncodeWord stmtSimAppendStorageCompose abiTupleProps
  bodyPtrDefs supportedTypes valueEncoding valueEncodingProps valueEncodingDefs
  vyperValue vyperTyping vyperAST vyperState venomState finite_map list words arithmetic
  abiDecodeStaticProps entryDecodeStaticProps appendStorageStageTransportPtr bodyMemoryDefs
  dynCopyExec loweringShapeDefs ptrDiscipline stateFrame valueEncodingProofs
  valueEncodingTyping vyperLookup

Theorem type_stmt_append_name[local]:
  type_stmt env ret_ty (Append (NameTarget id) e) =
    (case type_place_target env (NameTarget id) of
     | SOME (Type (ArrayT elem_ty (Dynamic n))) =>
         if target_mutable env (NameTarget id) /\ well_typed_expr env e /\
            type_widens_to env.type_defs (expr_type e) elem_ty /\
            assignable_type env.type_defs elem_ty then SOME env else NONE
     | _ => NONE)
Proof
  simp[Once vyperTypeSystemTheory.type_stmt_def]
QED

Theorem append_local_word_ghost_inputs[local]:
  expr_sim_pre ce cx env (Name (ArrayT elem (Dynamic cap)) id) es /\
  is_word_type elem /\ stmt_state_rel H ctx func ce cx es s /\
  ghost_inv_at D lo d ce cx es G tn s ==>
  ?entry p sz bp tv vs.
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = ArrayTV tv (Dynamic cap) /\
    entry.value = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) elem = SOME tv /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME bp /\ type_memory_size tv = 32 /\
    ptr_covers G tn p s (32*(1+cap)) /\
    (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
    w2n bp+32*(1+cap) <= s.vs_alloca_next
Proof
  strip_tac >> drule_all body_name_source_region >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
        entry.type = ArrayTV tv (Dynamic cap)` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  `?vs. entry.value = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type entry.type entry.value` mp_tac >>
     simp[] >> Cases_on `entry.value` >> simp[value_has_type_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >> simp[value_has_type_def]) >>
  `type_memory_size tv = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n w) mem = n2w (LENGTH vs)` by
    (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `sz`, `w`, `tv`, `vs`] >>
  simp[] >> conj_tac
  >- (gvs[ptr_covers_def, type_memory_size_def] >> metis_tac[LESS_EQ_TRANS]) >>
  gvs[type_memory_size_def] >> decide_tac
QED

Theorem append_local_word_robust_array:
  (!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) /\
  (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\ type_memory_size tv = 32 /\
  mem_word_at off new_memory = n2w (LENGTH vs+1) /\
  DISJOINT {i | off <= i /\ i < off+32} new_taint /\
  (!mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory tv v (off+32*(1+LENGTH vs)) mem) /\
  (!i. ~(off <= i /\ i < off+32) /\
       ~(off+32*(1+LENGTH vs) <= i /\
         i < off+32*(1+LENGTH vs)+32) ==>
    mem_bytes_at i 1 new_memory = mem_bytes_at i 1 old_memory /\
    (i IN new_taint <=> i IN old_taint)) ==>
  !mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) off mem
Proof
  strip_tac >> match_mp_tac robust_dynarray_clean_count_assemble >>
  simp[LENGTH_APPEND] >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [EL_APPEND_EQN] >>
      qpat_assum `!mem. mem_agree_outside new_taint new_memory mem ==> _` mp_tac >>
      simp_tac (srw_ss()) [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ADD_ASSOC, ADD_COMM]) >>
  `j < LENGTH vs` by decide_tac >>
  `val_wf tv (EL j vs)` by metis_tac[] >>
  `val_footprint tv (EL j vs) <= 32` by metis_tac[val_footprint_le] >>
  `!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory tv (EL j vs) (off+32+j*32) mem` by
    (rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem` by
       metis_tac[] >>
     `elems_in_memory vs (off+32) tv mem` by
       (qpat_assum `val_in_memory (ArrayTV tv (Dynamic cap))
          (ArrayV (DynArrayV vs)) off mem`
          (strip_assume_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def]) >>
        fs[]) >>
     drule_all elems_in_memory_EL >> simp[]) >>
  simp[EL_APPEND_EQN] >>
  match_mp_tac robust_val_in_memory_exterior_frame >>
  qexistsl_tac [`old_taint`, `old_memory`,
    `{i | off <= i /\ i < off+32} UNION
     {i | off+32*(1+LENGTH vs) <= i /\
          i < off+32*(1+LENGTH vs)+32}`] >>
  simp[] >>
  qpat_x_assum `!mem. mem_agree_outside old_taint old_memory mem ==> _` mp_tac >>
  simp_tac (srw_ss()) [DECIDE ``off+32+j*32 = 32*j+(off+32)``]
QED

Theorem body_append_local_primitive_full:
  !cx id e.
    is_word_type (expr_type e) /\
    (!s0 p s1. eval_target_place cx (NameTarget id) s0 = (INL p,s1) ==>
                  body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rpt strip_tac >> rw[body_stmt_full_ok_def] >>
  rw[stmt_frag_full_def] >>
  `~(?nm. NameTarget id = TopLevelNameTarget nm)` by simp[] >>
  drule_all body_append_word_pre >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  `FLOOKUP env.var_types id = SOME (ArrayT (expr_type e) (Dynamic cap))` by
    gvs[Once vyperTypeSystemTheory.well_typed_expr_def, AllCaseEqs()] >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  `eval_target_place cx (NameTarget id) es =
     (INL (MemoryPlace id []),es)` by
    (irule exprSimPopTheory.eval_target_place_name >> simp[]) >>
  `body_expr_full_ok cx e` by metis_tac[] >>
  `cenv.ce_var_type id = SOME (ArrayT (expr_type e) (Dynamic cap))` by
    fs[expr_sim_inv_def] >>
  `compile_get_target_ptr compile_expr cenv (NameTarget id) sa =
    ((Var p,SOME LocMemory,SOME (ValPT (ArrayT (expr_type e) (Dynamic cap)))) ,sa)` by
    simp[compile_get_target_ptr_def, comp_return_def] >>
  drule_all stmtSimAppendResolvedTheory.append_resolved_word_code_parts >> strip_tac >>
  gvs[] >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value compile_expr _ _
    (gas_shadow_expr e) shadow_sa = (shadow_op,shadow_sm)` >>
  `shadow_op = vop /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = (vop,sm)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _`
       (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  gvs[] >>
  `compile_dynarray_append cenv (Var p) shadow_op 32 32 (expr_type e)
     (lowered_value_type cenv e) cap T LocMemory sm = ((),sb)` by
    (drule abi_builtin_encode_word_info >> strip_tac >>
     fs[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
        contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def]) >>
  drule append_memory_word_footprint >> strip_tac >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `cs_extends sm sb` by
    (simp[cs_extends_def] >> qexists_tac `[]` >>
     fs[emitHelperPropsTheory.inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa sm func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  rewrite_tac[Once vyperInterpreterTheory.evaluate_def,
              vyperStateTheory.bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- suspend "append_storage_frame" >>
  conj_tac >- suspend "place_bind_cert" >>
  conj_tac >- suspend "place_error_cert" >>
  conj_tac >- suspend "place_storage_frame" >>
  qexists_tac `\H res mid G tn t.
    res = INL (MemoryPlace id []) /\ mid = (es with gas_obs := []) /\
    G = G0 /\ tn = tn0 /\ t = s0` >>
  conj_tac >- suspend "rhs_full" >>
  suspend "place_full"
QED

Resume body_append_local_primitive_full[place_full]:
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (MemoryPlace id [])`, `s0`, `tn0`] >>
  conj_tac
  >- (gen_tac >> irule exprSimPopTheory.eval_target_place_name >> simp[]) >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]
QED

Resume body_append_local_primitive_full[place_storage_frame]:
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
QED

Resume body_append_local_primitive_full[append_storage_frame]:
  simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_append_place]
QED

Resume body_append_local_primitive_full[place_error_cert]:
  metis_tac[gasExemptCertTheory.gas_exempt_cert_error_place]
QED

Resume body_append_local_primitive_full[place_bind_cert]:
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
  goal_assum (drule_at Any) >> fs[]
QED

Resume body_append_local_primitive_full[rhs_full]:
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >> gvs[] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  `compile_dynarray_append cenv (Var p) shadow_op
      (word_scale LocMemory) (elem_size_in_location cenv LocMemory (expr_type e))
      (expr_type e) (lowered_value_type cenv (gas_shadow_expr e)) cap T
      LocMemory shadow_sm =
      ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_sa = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_stmt_def, gasShadowTheory.gas_shadow_expr_def, stmt_env_def, stmtLoweringTheory.declare_stmt_local_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          Once stmtLoweringTheory.compile_stmt_def, compile_get_target_ptr_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     rename1 `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = (u,_)` >>
     Cases_on `u` >> simp[]) >>
  `cs_extends shadow_sm shadow_sb` by
    (drule abi_builtin_encode_word_info >> strip_tac >>
     fs[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
        contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def] >>
     drule append_memory_word_footprint >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >>
     fs[emitHelperPropsTheory.inst_extends_def, same_blocks_def]) >>
  `cs_extends shadow_sa shadow_sm` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` mp_tac >>
     qspecl_then [`gas_shadow_env T cenv`, `expr_type e`,
                  `gas_shadow_expr e`, `shadow_sa`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gasContextTheory.gas_admissible_def] >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     `eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
       (INL (MemoryPlace id []),es with gas_obs := gs)` by
       (irule exprSimPopTheory.eval_target_place_name >> simp[]) >>
     qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gasContextTheory.gas_admissible_def] >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_assoc,
          exprSimPopTheory.eval_target_place_name] >>
     simp[GSYM vyperStateTheory.bind_assoc, Once vyperStateTheory.bind_def] >>
     strip_tac >>
     qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def] >>
     Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     imp_res_tac vyperExprNoControlTheory.read_result_no_control >>
     imp_res_tac (cj 1 vyperExprNoControlTheory.eval_expr_no_control) >>
     Cases_on `y` >>
     gvs[vyperExprNoControlTheory.no_control_exc_def, expr_res_ok_def,
         stmtSimDefsTheory.stmt_res_ok_def] >>
     gvs[vyperStateTheory.bind_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e (es with gas_obs := [])` by
    (`body_const_cells_agree [(NONE,tops)] cx env (es with gas_obs := [])` by
       simp[body_const_cells_agree_state_updates] >>
     `expr_body_pre cenv cx env e (es with gas_obs := [])` by
       simp[expr_body_pre_gas_obs] >>
     drule_all body_expr_full_ok_simulations >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                         `shadow_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[ret_pc_ok_def] >>
     reverse conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `H` mp_tac) >> simp[] >> strip_tac
         >- (qsuff_tac `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
                           storage_well_formed_on cx es (FST H)`
             >- simp[] >>
             irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[])
         >> fs[ghost_inv_at_def] >> metis_tac[]) >>
     metis_tac[])) >>
  strip_tac >>
  `return_buf_sep d cenv (es with gas_obs := []) s0` by
    simp[return_buf_sep_gas_obs] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv (es with gas_obs := []) s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 R1` >>
  irule (Q.INST [`es` |-> `es with gas_obs := []`] gas_outcome_full_bind_all) >>
  conj_tac >- suspend "value_storage_frame" >>
  conj_tac >- suspend "value_bind_cert" >>
  conj_tac >- suspend "value_error_cert" >>
  conj_tac >- suspend "rhs_storage_frame" >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th =>
    irule_at (Pos last) gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    irule_at (Pos hd) th) >>
  qexists_tac `\H res ee G tn t. Q1 H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "rhs_exit" >>
  simp[Abbr `Q1`] >> suspend "append_suffix"
QED

Resume body_append_local_primitive_full[value_storage_frame]:
  simp[vyperStorageTraceTheory.storage_trace_frame_append_place]
QED

Resume body_append_local_primitive_full[rhs_storage_frame]:
  simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]
QED

Resume body_append_local_primitive_full[value_error_cert]:
  metis_tac[gasExemptCertTheory.gas_exempt_cert_error_value]
QED

Resume body_append_local_primitive_full[value_bind_cert]:
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> fs[]
QED

Resume body_append_local_primitive_full[rhs_exit]:
  simp[Abbr `R1`] >> rpt gen_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `res` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[expr_exit_def, stmt_exit_ptr_def, halt_exit_def] >>
  all_tac >~ [`Error err`]
  >- (Cases_on `err` >> simp[stmt_exit_ptr_def, expr_exit_def, halt_exit_def]) >>
  simp[]
QED

Resume body_append_local_primitive_full[append_suffix]:
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >> gvs[] >>
  qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
    (qspec_then `[]` assume_tac) >>
  fs[APPEND_NIL] >>
  `expr_sim_inv cenv cx env mid /\ value_runtime_typed env (expr_type e) v` by
    (`expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks' s0.vs_gas_readings)` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_eval >>
     disch_then (qspecl_then [`INL v`, `mid with gas_obs := []`] mp_tac) >>
     (impl_tac >- (qpat_assum `bind _ _ _ = (INL v,_)` mp_tac >>
                   simp[NoAsms, vyperStateTheory.bind_def])) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  gvs[] >>
  `expr_sim_pre cenv cx env (Name (ArrayT (expr_type e) (Dynamic cap)) id) mid` by
    (simp[expr_sim_pre_body, expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
          byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
          vyperTypeCallGraphTheory.int_calls_expr_def,
          supportedExprTraverseTheory.expr_has_evm_run_thm,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedProgramTheory.expr_abi_decode_target_root_def,
          const_name_root_def] >>
     fs[expr_body_pre_def, bodySimTheory.locals_alloc_ok_def,
        allocLimitsTheory.type_alloc_ok_def,
        vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
        compileEnvTheory.type_bits_def] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx mid t` by fs[expr_post_def] >>
  drule_all append_local_word_ghost_inputs >> strip_tac >>
  gvs[] >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id [])) bp (SOME LocMemory)
     (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    (simp[place_ptr_rel_def, mem_path_offset_def, evaluate_type_def, WORD_ADD_0]) >>
  `evaluate_subscripts entry'.type entry'.value [] = INL (ArrayV (DynArrayV vs))` by
    simp[evaluate_subscripts_def] >>
  drule_all append_memory_word_layout >> strip_tac >> gvs[] >>
  `not_fresh_at sm p` by
    (irule freshWritesTheory.not_fresh_at_mono >> goal_assum (drule_at Any) >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x. Var p = Var x \/ shadow_op = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[]) >>
  `eval_operand (Var p) t = SOME bp` by simp[venomStateTheory.eval_operand_def] >>
  `?w. eval_operand shadow_op t = SOME w` by
    (fs[expr_post_def, expr_val_rel_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (`alloca_room ctx func t` by fs[stmt_state_rel_def] >>
     qpat_x_assum `alloca_room ctx func t` mp_tac >>
     pure_rewrite_tac[alloca_room_def] >> strip_tac >> decide_tac) >>
  `w2n bp + 32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all append_memory_word_run_reserved >> strip_tac >>
  `w2n bp + 32*(1+cap) <= t.vs_alloca_next` by decide_tac >>
  drule_all append_memory_word_mem_ok >> strip_tac >>
  `ptr_covers G1 tn1 p t (32*(1+cap))` by
    (qpat_assum `ptr_covers _ _ _ _ _` mp_tac >> simp[ADD_COMM]) >>
  `op_taint tn1 shadow_op = {}` by fs[ptr_val_ok_def] >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all (Q.INST [`D` |-> `DF (storage_trace_horizon mid.storage_trace)`,
                     `fn` |-> `func`, `PG` |-> `PG`] append_memory_word_ptr) >>
  disch_then (qspecl_then [`mid`, `func`, `PG`, `DF`] strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G1 tn1
       (emitted_insts sm sb) (t with vs_inst_idx := k) Gf tnf` by
    (rpt gen_tac >>
     drule_all append_memory_word_ptr >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr (DF _) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]) >>
  `mload (w2n bp) t = n2w (LENGTH vs)` by
    (qpat_assum `val_in_memory (ArrayTV _ _) _ _ _` mp_tac >>
     pure_rewrite_tac[val_in_memory_def] >> strip_tac >>
     fs[venomStateTheory.mload_def, mem_word_at_def]) >>
  `LENGTH vs <= cap /\ LENGTH vs < dimword (:256)` by
    (fs[value_has_type_def] >> decide_tac) >>
  `w2n (mload (w2n bp) t) = LENGTH vs` by simp[] >>
  `!st. st.scopes = mid.scopes ==>
     place_type_value cx (MemoryPlace id []) st = (INL (ArrayTV tv (Dynamic cap)),st) /\
     read_place cx (MemoryPlace id []) st = (INL (ArrayV (DynArrayV vs)),st)` by
    (rpt strip_tac >>
     simp[place_type_value_def, read_place_def, get_scopes_def,
          lift_option_type_def, lift_option_def, bind_def, return_def,
          subscripts_type_def, read_memory_path_def, evaluate_subscripts_def,
          lift_sum_def]) >>
  `!st. st.scopes = mid.scopes ==>
     append_place cx (MemoryPlace id []) v st =
     bind (lift_sum (append_element (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) v))
          (write_place cx (MemoryPlace id [])) st` by
    (rpt strip_tac >> simp[append_place_def, bind_def]) >>
  Cases_on `LENGTH vs < cap`
  >- suspend "append_success"
  >> suspend "append_full"
QED

Resume body_append_local_primitive_full[append_full]:
  rpt strip_tac >>
  `!st. st.scopes = mid.scopes ==>
    append_place cx (MemoryPlace id []) v st =
      (INR (Error (RuntimeError "append overflow")),st)` by
    (rpt strip_tac >> simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
                          bind_def, lift_sum_def, raise_def] >> decide_tac) >>
  qpat_assum `compile_dynarray_append _ _ _ 32 32 _ _ _ _ _ sm = _` mp_tac >>
  simp[NoAsms, compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> disch_then assume_tac >>
  qabbrev_tac `i0 = mk_inst sm.cs_next_id MLOAD [Var p]
     [STRING #"%" (toString sm.cs_next_var)]` >>
  qabbrev_tac `i1 = mk_inst (sm.cs_next_id+1) LT
     [Var (STRING #"%" (toString sm.cs_next_var)); Lit (n2w cap)]
     [STRING #"%" (toString (sm.cs_next_var+1))]` >>
  qabbrev_tac `i2 = mk_inst (sm.cs_next_id+2) ASSERT
     [Var (STRING #"%" (toString (sm.cs_next_var+1)))] []` >>
  `?rest. emitted_insts sm sb = i0::i1::i2::rest` by
    (qpat_x_assum `sm with <|cs_next_var := _; cs_next_id := _; cs_current_insts := _|> = sb` mp_tac >>
     disch_then (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  `?u0. step_inst_base i0 t = OK u0` by
    simp[Abbr `i0`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def] >>
  `?u1. step_inst_base i1 u0 = OK u1` by
    (qpat_x_assum `step_inst_base i0 t = OK u0` mp_tac >>
     simp[Abbr `i0`, Abbr `i1`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
          venomExecSemanticsTheory.exec_pure2_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     disch_then (SUBST1_TAC o SYM) >> simp[FLOOKUP_UPDATE]) >>
  `step_inst_base i2 u1 = Abort Revert_abort (revert_state (set_returndata [] u1))` by
    (qpat_assum `step_inst_base i1 u0 = OK u1` mp_tac >>
     qpat_assum `step_inst_base i0 t = OK u0` mp_tac >>
     simp[NoAsms, Abbr `i0`, Abbr `i1`, Abbr `i2`,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
          venomExecSemanticsTheory.exec_pure2_def, update_var_def] >>
     qpat_assum `eval_operand (Var p) t = SOME bp` mp_tac >>
     qpat_assum `mload (w2n bp) t = _` mp_tac >>
     qpat_assum `LENGTH vs < dimword _` mp_tac >>
     qpat_assum `~(LENGTH vs < cap)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
         venomExecSemanticsTheory.bool_to_word_def]) >>
  `inst_mem_below_frontier i0 t /\ inst_dload_in_section i0 t /\
   inst_mem_below_frontier i1 u0 /\ inst_dload_in_section i1 u0 /\
   inst_mem_below_frontier i2 u1 /\ inst_dload_in_section i2 u1` by
    (qpat_assum `run_inst_seq_mem_ok _ t` mp_tac >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >> simp[]) >>
  qabbrev_tac `j0 = SUC t.vs_inst_idx` >> qabbrev_tac `j1 = SUC j0` >>
  qabbrev_tac `Ga = step_prov PG G1 i0 u0` >>
  qabbrev_tac `tna = step_taint i0 t u0 tn1` >>
  qabbrev_tac `Gb = step_prov PG Ga i1 u1` >>
  qabbrev_tac `tnb = step_taint i1 (u0 with vs_inst_idx := j0) (u1 with vs_inst_idx := j0) tna` >>
  `~is_terminator i0.inst_opcode /\ ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G1 tn1 i0 t /\
       ptr_inst_ok D lo 0 ctx func Ga tna i1 (u0 with vs_inst_idx := j0) /\
       ptr_inst_ok D lo 0 ctx func Gb tnb i2 (u1 with vs_inst_idx := j1) /\
       Gf = Gb /\ tnf = tnb` by
    (gen_tac >>
     qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     simp[fragGasSeqPtrTheory.inst_seq_ptr_def,
          instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
          ghostPcTransportPtrTheory.step_prov_inst_idx,
          Abbr `j0`, Abbr `j1`, Abbr `Ga`, Abbr `Gb`, Abbr `tna`, Abbr `tnb`]) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME i0 /\
        get_instruction bb j0 = SOME i1 /\ get_instruction bb j1 = SOME i2` by
    (drule fragExecTheory.fn_has_code_same_block >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
     (impl_tac >- fs[same_blocks_def, inst_extends_def]) >>
     strip_tac >> qexists_tac `bb` >>
     qpat_x_assum `!i. i < LENGTH _ ==> _` mp_tac >>
     qpat_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
     simp[Abbr `j0`, Abbr `j1`] >> disch_tac >>
     qpat_assum `!i. i < _ ==> get_instruction _ _ = _` (qspec_then `0` assume_tac) >>
     qpat_assum `!i. i < _ ==> get_instruction _ _ = _` (qspec_then `1` assume_tac) >>
     qpat_x_assum `!i. i < _ ==> get_instruction _ _ = _` (qspec_then `2` assume_tac) >>
     qpat_x_assum `0 < _ ==> _` mp_tac >>
     qpat_x_assum `1 < _ ==> _` mp_tac >>
     qpat_x_assum `2 < _ ==> _` mp_tac >> rpt (pop_assum kall_tac) >>
     `SUC (SUC (LENGTH sm.cs_current_insts)) = LENGTH sm.cs_current_insts + 2` by decide_tac >>
     simp[GSYM arithmeticTheory.ADD1]) >>
  `i0.inst_opcode = MLOAD /\ i1.inst_opcode = LT /\ i2.inst_opcode = ASSERT` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, venomInstTheory.mk_inst_def] >>
  `~t.vs_halted` by fs[expr_post_def] >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (t,G1,tn1) [] (OK (u0 with vs_inst_idx := j0),Ga,tna)` by
    (qpat_assum `step_inst_base i0 t = OK u0` mp_tac >>
     qpat_assum `~t.vs_halted` mp_tac >>
     qpat_assum `lookup_block sm.cs_current_bb _ = SOME bb` mp_tac >>
     qpat_assum `t.vs_current_bb = sm.cs_current_bb` mp_tac >>
     qpat_assum `get_instruction bb t.vs_inst_idx = SOME i0` mp_tac >>
     qpat_assum `i0.inst_opcode = MLOAD` mp_tac >>
     qpat_assum `~is_terminator i0.inst_opcode` mp_tac >>
     qpat_assum `inst_mem_below_frontier i0 t` mp_tac >>
     qpat_assum `inst_dload_in_section i0 t` mp_tac >>
     qpat_assum `!D. ptr_inst_ok D _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     simp[NoAsms, Abbr `j0`, Abbr `Ga`, Abbr `tna`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     first_assum (mp_then (Pat `step_inst_base _ _ = _`) mp_tac
       fragGasSeqPtrTheory.straight_line_origin_ptr_edge) >> simp[]) >>
  `~u0.vs_halted /\ u0.vs_current_bb = t.vs_current_bb /\
   ~u1.vs_halted /\ u1.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstProofs1Theory.step_inst_base_preserves_all] >>
  `step_inst_base i1 (u0 with vs_inst_idx := j0) = OK (u1 with vs_inst_idx := j0)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def] >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (u0 with vs_inst_idx := j0,Ga,tna) [] (OK (u1 with vs_inst_idx := j1),Gb,tnb)` by
    (qpat_assum `step_inst_base i1 (u0 with vs_inst_idx := j0) = _` mp_tac >>
     qpat_assum `~u0.vs_halted` mp_tac >>
     qpat_assum `lookup_block sm.cs_current_bb _ = SOME bb` mp_tac >>
     qpat_assum `u0.vs_current_bb = t.vs_current_bb` mp_tac >>
     qpat_assum `t.vs_current_bb = sm.cs_current_bb` mp_tac >>
     qpat_assum `get_instruction bb j0 = SOME i1` mp_tac >>
     qpat_assum `i1.inst_opcode = LT` mp_tac >>
     qpat_assum `~is_terminator i1.inst_opcode` mp_tac >>
     qpat_assum `inst_mem_below_frontier i1 u0` mp_tac >>
     qpat_assum `inst_dload_in_section i1 u0` mp_tac >>
     qpat_assum `!D. ptr_inst_ok D _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     simp[NoAsms, Abbr `j1`, Abbr `Gb`, Abbr `tnb`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     first_assum (mp_then (Pat `step_inst_base _ _ = _`) mp_tac
       fragGasSeqPtrTheory.straight_line_origin_ptr_edge) >>
     simp[ghostPcTransportPtrTheory.step_prov_inst_idx]) >>
  qabbrev_tac `uf = revert_state (set_returndata [] (u1 with vs_inst_idx := j1))` >>
  `step_inst_base i2 (u1 with vs_inst_idx := j1) = Abort Revert_abort uf` by
    simp[Abbr `uf`, instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def, revert_state_def, set_returndata_def] >>
  `!D explicit. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (u1 with vs_inst_idx := j1,Gb,tnb) [] (Abort Revert_abort uf,Gb,tnb)` by
    (rpt gen_tac >> simp[fragGasOriginPtrTheory.gas_origin_ptr_edge_def] >>
     conj_tac >-
       (pure_rewrite_tac[fragGasOriginTheory.gas_origin_edge_def] >>
        conj_tac >- simp[] >>
        qexistsl_tac [`0`, `bb`, `i2`, `Abort Revert_abort uf`] >>
        simp[venomExecSemanticsTheory.step_inst_non_invoke, gasEventsTheory.gas_events_step_def,
             memSafeRunTheory.mem_safe_step_non_invoke, fragExecTheory.exit_result_def]) >>
     pure_rewrite_tac[fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     conj_tac >- simp[] >>
     qexistsl_tac [`0`, `bb`, `i2`, `Abort Revert_abort uf`] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          ptrSafeRunTheory.ptr_safe_step_def, fragExecTheory.exit_result_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (t,G1,tn1) [] (Abort Revert_abort uf,Gb,tnb)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (t,G1,tn1) _ _` mp_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (u0 with vs_inst_idx := j0,Ga,tna) _ _` mp_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_edge _ (u1 with vs_inst_idx := j1,Gb,tnb) _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules, APPEND, fragExecTheory.exit_result_def]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gb`, `mid`, `Abort Revert_abort uf`,
                `INR (Error (RuntimeError "append overflow"))`, `tnb`] >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def]
QED

Resume body_append_local_primitive_full[append_success]:
  qpat_assum `!len. _ /\ _ ==> ?u. _` (qspec_then `LENGTH vs` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sm sb func` mp_tac >>
     pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >>
     fs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     gvs[emitted_insts_def] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    (qpat_assum `EVERY _ (emitted_insts sm sb)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, FILTER_EQ_NIL] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G1,tn1) []
      (OK (u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sb)),Gf,tnf)` by
    (rpt gen_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm sb) t = OK u`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac
         fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path) >>
     simp[] >> disch_then irule >> conj_tac
     >- (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         qpat_x_assum `EVERY (\i. i.inst_opcode = MLOAD \/ _) (emitted_insts sm sb)` mp_tac >>
         qpat_assum `emitted_insts sm sb = _` mp_tac >>
         rpt (pop_assum kall_tac) >> disch_then SUBST1_TAC >>
         simp[EVERY_APPEND] >> rpt strip_tac >> fs[]) >>
     conj_tac >- (qexists_tac `bb` >> metis_tac[]) >>
     qpat_assum `!D k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`, `t.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
  `value_has_type tv v` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >> gvs[]) >>
  `entry'.assignable` by
    (`FLOOKUP env.var_assignable id = SOME T` by
        fs[type_stmt_append_name, vyperTypeSystemTheory.target_mutable_def] >>
      fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
      qpat_x_assum `!id. FLOOKUP env.var_assignable id = SOME T ==> ?en. lookup_scopes id mid.scopes = SOME en /\ en.assignable`
        (qspec_then `id` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  drule vyperLookupTheory.lookup_scopes_find_containing_scope >> strip_tac >>
  qabbrev_tac `ff = mid with scopes := pre ++
    (env'' |+ (id,entry' with <|value := ArrayV (DynArrayV (vs ++ [v])); popped := []|>)) :: rest` >>
  `!tail. write_place cx (MemoryPlace id []) (ArrayV (DynArrayV (vs ++ [v])))
      (mid with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
    simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
         lift_option_type_def, type_check_def, assert_def, lift_sum_def,
         replace_memory_entry_def, evaluate_subscripts_def,
         assign_subscripts_def, set_scopes_def, return_def, Abbr `ff`] >>
  `!tail. append_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    (gen_tac >> first_x_assum (qspec_then `mid with gas_obs := tail` mp_tac) >>
     simp[vyperValueOperationTheory.append_element_def, compatible_bound_def,
          safe_cast_well_typed, SNOC_APPEND, bind_def, lift_sum_def, return_def]) >>
  `ff.storage_trace = mid.storage_trace` by simp[Abbr `ff`] >>
  `post_value_type cenv e = expr_type e` by
    simp[post_value_type_def, lowered_value_type_def] >>
  `w = typed_val_to_w256 tv v` by
    (qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`post_value_type cenv e = expr_type e`, `is_word_type (expr_type e)`,
        `evaluate_type (get_tenv cx) (expr_type e) = SOME tv`,
        `eval_operand shadow_op t = SOME w`] >>
     rpt (pop_assum kall_tac) >> simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `abi_tuple_word tv v` by
    (qpat_assum `is_word_type (expr_type e)` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` mp_tac >>
     qpat_assum `value_has_type tv v` mp_tac >> rpt (pop_assum kall_tac) >>
     Q.SPEC_TAC (`expr_type e`, `ty`) >> Cases_on `ty` >>
     simp[is_word_type_def, evaluate_type_def, AllCaseEqs()]
     >~ [`FlagTV`] >-
       (rpt strip_tac >> Cases_on `v` >> gvs[value_has_type_def, abi_tuple_word_def]) >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
     rpt strip_tac >> Cases_on `v` >> gvs[value_has_type_def, abi_tuple_word_def]) >>
  `u.vs_alloca_next = t.vs_alloca_next /\ u.vs_allocas = t.vs_allocas` by
    (qpat_assum `state_frame u = _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[stateFrameTheory.state_frame_def, dynCopyExecTheory.mstore_control_fields]) >>
  `!idx. ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := idx)` by
    (`u.vs_initial_fmp = t.vs_initial_fmp /\ u.vs_fmp = t.vs_fmp` by
       (qpat_assum `state_frame u = _`
          (mp_tac o AP_TERM ``\s:venom_state. (s.vs_initial_fmp,s.vs_fmp)``) >>
        simp_tac std_ss [stateFrameTheory.state_frame_def, mstore_def,
          write_memory_with_expansion_def, LET_THM, venom_state_accfupds,
          pairTheory.PAIR_EQ]) >>
     gen_tac >> disch_tac >>
     `allocas_below_fmp (u with vs_inst_idx := idx) = allocas_below_fmp t` by
       (pure_rewrite_tac [allocas_below_fmp_def, venom_state_accfupds] >>
        map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac [th]))
          [`u.vs_initial_fmp = t.vs_initial_fmp`, `u.vs_fmp = t.vs_fmp`,
           `u.vs_allocas = t.vs_allocas`] >> REFL_TAC) >>
     pop_assum SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t`
       (fn bound => qpat_assum `ctx_has_dalloca ctx` (ACCEPT_TAC o MP bound))) >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `ghost_kept_at lo cenv _ sa G0 tn0 s0 G1 tn1`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` mp_tac >>
     qpat_assum `sa.cs_next_var <= sm.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
      lookup_var x (u with vs_inst_idx :=
        LENGTH sm.cs_current_insts + LENGTH (emitted_insts sm sb)) = SOME z` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `lookup_var x t = SOME z` by (fs[expr_post_def] >> metis_tac[]) >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `ff`, `INL ()`,
    `u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sb)`, `tnf`] >>
  conj_tac >- simp[] >> simp[] >> rpt strip_tac >>
  all_tac >~ [`stmt_lands _ _ _ _`]
  >- (map_every (fn q => qpat_assum q mp_tac)
        [`same_blocks sm sb`, `inst_extends sm sb`, `t.vs_current_bb = _`] >>
      qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``\s:venom_state. s.vs_current_bb``) >>
      rpt (pop_assum kall_tac) >> pure_rewrite_tac[same_blocks_def, inst_extends_def] >>
      rpt strip_tac >> simp[stmt_lands_def] >>
      gvs[stateFrameTheory.state_frame_def, dynCopyExecTheory.mstore_control_fields]) >>
  all_tac >~ [`F`]
  >- (qpat_assum `run_inst_seq _ t = OK u`
        (mp_then Any mp_tac fragExecTheory.run_inst_seq_preserves_halted) >> simp[]) >>
  all_tac >~ [`cenv_top_ext _ _ _`] >- simp[cenv_top_ext_def] >>
  all_tac >~ [`stmt_state_rel _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      `stmt_state_rel H ctx func cenv cx mid t` by fs[expr_post_def] >>
      `stmt_state_rel H ctx func cenv cx ff
        (mstore (w2n bp) (n2w (LENGTH vs+1))
          (mstore (w2n bp+32*(1+LENGTH vs)) w t))` by
        (irule append_memory_word_state >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `expr_sim_inv cenv cx env mid` (irule_at Any) >>
         simp[] >> qexistsl_tac [`v`, `tv`, `cap`] >> simp[abi_tuple_word_mstore] >>
         conj_tac >- gvs[evaluate_type_def] >>
         conj_tac >-
           (qpat_assum `evaluate_type _ (ArrayT _ _) = SOME entry.type` mp_tac >>
            qpat_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
            rpt (pop_assum kall_tac) >> strip_tac >> simp[evaluate_type_def]) >>
         conj_tac
         >- (qpat_assum `!tail. write_place _ _ _ _ = _`
               (qspec_then `mid.gas_obs` mp_tac) >> simp[NoAsms, Abbr `ff`]) >>
         fs[value_has_type_def, all_have_type_EVERY, EVERY_APPEND]) >>
      simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_reserved_frame >>
      qpat_assum `stmt_state_rel H ctx func cenv cx ff (mstore _ _ _)` (irule_at Any) >>
      qexists_tac `sm` >> conj_tac
      >- (qpat_assum `!x a. not_fresh_at sm x /\ _ ==> _` mp_tac >>
          rpt (pop_assum kall_tac) >> simp[lookup_var_def, mstore_def]) >>
      conj_tac >- (qpat_assum `state_frame u = _` ACCEPT_TAC) >>
      irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
      qexists_tac `sa` >> simp[]) >>
  all_tac >~ [`storage_well_formed_on _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      `storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
      irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
      qexists_tac `mid` >> simp[Abbr `ff`]) >>
  all_tac >~ [`return_buf_frame _ _ _ _`]
  >- (`return_buf_frame d cenv sm t` by
        (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> fs[expr_post_def]) >>
      irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `t`, `sm`] >> simp[] >>
      qpat_assum `!x a. not_fresh_at sm x /\ _ ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[lookup_var_def]) >>
  all_tac >~ [`alloca_history _ _`]
  >- (`alloca_inv t` by fs[stmt_state_rel_def] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      qpat_assum `run_inst_seq _ t = OK u` (mp_then Any mp_tac alloca_history_run_inst_seq) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `bb` >>
      qpat_assum `emitted_insts sm sb ≼ _` mp_tac >>
      qpat_assum `lookup_block t.vs_current_bb _ = _` mp_tac >>
      qpat_assum `t.vs_current_bb = _` mp_tac >> qpat_assum `t.vs_inst_idx = _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  all_tac >~ [`return_buf_sep _ _ _ _`]
  >- (`MAP FDOM mid.scopes = MAP FDOM es.scopes` by
        (qpat_assum `bind (eval_expr cx e) _ _ = _`
           (mp_then Any mp_tac eval_read_preserves_scopes_dom) >> simp[]) >>
      `MAP FDOM ff.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `!tail. write_place _ _ _ _ = _`
           (qspec_then `[]` (mp_then Any mp_tac write_place_scopes_dom)) >>
         simp[]) >>
      `MAP FDOM ff.scopes = MAP FDOM es.scopes` by simp[] >>
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
         es.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
        (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
           (drule_then (ACCEPT_TAC o cj 1))) >>
      irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
      conj_tac
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `!bw capacity. d = SOME (bw,capacity) ==> _`
            (qspecl_then [`bw`,`capacity`] mp_tac) >>
          pure_rewrite_tac[allocas_from_def] >>
          simp[arithmeticTheory.ADD_COMM]) >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`es`,
                    `func`,`s0`,`sa`] >>
      simp[]) >>
  all_tac >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
  >- (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      `local_region cenv mid.scopes t id (w2n bp) sz` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      `local_ptrs_rel func cenv mid.scopes t` by
        metis_tac[expr_post_def, stmt_state_rel_local_ptrs_alloca] >>
      `lo <= u.vs_alloca_next /\ allocas_from lo u` by
        (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
         qpat_assum `u.vs_alloca_next = _` mp_tac >> qpat_assum `u.vs_allocas = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
      `stor_taint_ok_at (DF H) tnf u` by
        (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
         qpat_assum `state_frame u = _` mp_tac >>
         map_every (fn q => qpat_assum q mp_tac)
           [`tnf.t_stor = _`, `tnf.t_trans = _`, `tnf.t_imm = _`] >>
         rpt (pop_assum kall_tac) >>
         simp_tac std_ss [ghost_inv_at_def, stor_taint_ok_at_def,
              stateFrameTheory.state_frame_def, mstore_def, LET_THM,
              venom_state_accfupds, venom_state_component_equality] >> metis_tac[]) >>
      simp[Abbr `ff`] >> irule body_full_local_scope_ghost_post >> simp[] >>
      conj_tac >-
        (qpat_assum `stor_taint_ok_at (DF H) tnf u` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[stor_taint_ok_at_def]) >>
      qexistsl_tac [`G1`, `bp`, `func`, `sz`, `t`, `sa`, `tn1`] >> simp[] >>
      conj_tac >- suspend "robust_array" >>
      conj_tac >- suspend "scope_old_vars" >>
      conj_tac >- suspend "scope_memory_frame" >>
      conj_tac >- suspend "scope_low_frame" >>
      qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[ghost_inv_at_def] >> metis_tac[]) >>
  all_tac >~ [`alloca_frame _ _ _ _ _ _ _`]
  >- suspend "success_alloca_frame" >>
  all_tac >~ [`FLOOKUP _.vs_allocas _ = SOME _`]
  >- (fs[expr_post_def] >> metis_tac[]) >>
  simp[] >>
  qpat_assum `ghost_kept_at lo cenv _ sa G0 tn0 s0 G1 tn1`
    (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `tnf.t_mem SUBSET tn1.t_mem` mp_tac >>
  map_every (fn q => qpat_assum q mp_tac)
    [`FLOOKUP s0.vs_allocas _ = SOME (_,_)`, `_ < sa.cs_next_id`,
     `!n b sz'. local_region cenv es.scopes s0 n b sz' ==> _`,
     `_ <= i`, `i < _`, `i IN tn1.t_mem`] >>
  rpt (pop_assum kall_tac) >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Resume body_append_local_primitive_full[scope_old_vars]:
  gen_tac >> strip_tac >>
  `not_fresh_at sm x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >-
    (simp[lookup_var_def] >>
     irule (REWRITE_RULE [lookup_var_def]
       appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars) >>
     qexists_tac `emitted_insts sm sb` >> simp[] >>
     qpat_assum `compile_dynarray_append _ _ _ 32 32 _ _ _ _ _ sm = _` mp_tac >>
     qpat_assum `not_fresh_at sm x` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> disch_then (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[DECIDE ``n <= n+k``]) >>
  metis_tac[]
QED

Resume body_append_local_primitive_full[scope_memory_frame]:
  `32*(cap+1) <= sz` by
    (qpat_assum `local_ptrs_rel func cenv mid.scopes t` mp_tac >>
     qpat_assum `lookup_scopes id mid.scopes = _` mp_tac >>
     qpat_assum `FLOOKUP cenv.ce_vars id = _` mp_tac >>
     qpat_assum `lookup_var p t = _` mp_tac >>
     qpat_assum `entry'.type = _` mp_tac >>
     qpat_assum `type_memory_size tv = 32` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[loweringStateRelDefsTheory.local_ptrs_rel_def] >> rpt strip_tac >>
     `type_memory_size entry'.type <= sz` by metis_tac[] >>
     gvs[type_memory_size_def] >> decide_tac) >>
  gen_tac >> disch_tac >> conj_tac >-
    (qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
     simp_tac (srw_ss()) [stateFrameTheory.state_frame_def] >> disch_then SUBST1_TAC >>
     irule EQ_TRANS >> irule_at Any abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside >>
     conj_tac >- decide_tac >>
     irule abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside >> decide_tac) >>
  simp[] >> decide_tac
QED

Resume body_append_local_primitive_full[scope_low_frame]:
  `stmt_state_rel H ctx func cenv cx mid t` by fs[expr_post_def] >>
  `lo <= w2n bp` by
    (`dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
     `0 < sz` by
       (`type_memory_size entry'.type <= sz` by
          (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[]) >>
        gvs[type_memory_size_def] >> decide_tac) >>
     drule_all body_full_local_region_lower_bound >> simp[]) >>
  qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
  simp_tac (srw_ss()) [stateFrameTheory.state_frame_def] >> disch_then SUBST1_TAC >>
  simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]
QED

Resume body_append_local_primitive_full[robust_array]:
  pure_rewrite_tac [DECIDE ``LENGTH vs+1 = 1+LENGTH vs``, ADD_ASSOC] >>
  match_mp_tac (Q.INST [`old_taint` |-> `tn1.t_mem`,
    `old_memory` |-> `t.vs_memory`] append_local_word_robust_array) >>
  conj_tac >- (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac >-
    (`val_wf entry'.type entry'.value` by
       (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[]) >>
     qpat_x_assum `val_wf entry'.type entry'.value` mp_tac >>
     simp[] >> rpt (pop_assum kall_tac) >>
     simp[val_wf_def] >> metis_tac[exprSimPopTheory.elems_val_wf_EL]) >>
  simp[] >>
  `u.vs_memory = (mstore (w2n bp) (n2w (LENGTH vs+1))
      (mstore (w2n bp+32*(1+LENGTH vs)) w t)).vs_memory` by
    (qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
     simp_tac (srw_ss()) [stateFrameTheory.state_frame_def]) >>
  conj_tac >- simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  conj_tac >- SET_TAC[] >>
  conj_tac >-
    (gen_tac >> strip_tac >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
     conj_tac >-
       (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
     qexistsl_tac [`32`,
       `(mstore (w2n bp+32*(LENGTH vs+1)) (typed_val_to_w256 tv v) t).vs_memory`] >>
     simp[abi_tuple_word_mstore] >>
     qpat_assum `mem_agree_outside _ u.vs_memory mem` mp_tac >>
     qpat_assum `u.vs_memory = _` mp_tac >>
     qpat_assum `w = typed_val_to_w256 tv v` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `mem_bytes_at (w2n bp+32*(LENGTH vs+1)) 32 u.vs_memory =
       mem_bytes_at (w2n bp+32*(LENGTH vs+1)) 32
         (mstore (w2n bp+32*(LENGTH vs+1)) (typed_val_to_w256 tv v) t).vs_memory` by
       simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     pop_assum (SUBST1_TAC o SYM) >>
     irule LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> rpt strip_tac >>
     rename1 `i < 32` >>
     `mem_bytes_at (w2n bp+32*(LENGTH vs+1)+i) 1 u.vs_memory =
       mem_bytes_at (w2n bp+32*(LENGTH vs+1)+i) 1 mem` by
       (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[valueEncodingProofsTheory.EL_mem_bytes_at]) >>
  qpat_assum `u.vs_memory = _` mp_tac >> rpt (pop_assum kall_tac) >>
  strip_tac >> rpt strip_tac >> simp[] >>
  dep_rewrite.DEP_REWRITE_TAC [valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >> decide_tac
QED

Resume body_append_local_primitive_full[success_alloca_frame]:
  `?xs. mid.storage_trace = es.storage_trace ++ xs` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
      (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    fs[expr_post_def, locals_kept_def] >>
  `alloca_frame cenv es sa s0 cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       stmtSimDefsTheory.expr_post_alloca_frame) >>
     simp[] >>
     qexistsl_tac [`H`, `ctx`, `cx`, `e`, `func`, `shadow_op`, `sm`, `v`] >>
     simp[] >> fs[expr_post_def] >>
     conj_tac >- first_assum ACCEPT_TAC >> fs[locals_kept_def, popped_kept_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_region cenv mid.scopes t id (w2n bp) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv mid.scopes t` by
    metis_tac[expr_post_def, stmt_state_rel_local_ptrs_alloca] >>
  `32*(cap+1) <= sz` by
    (qpat_assum `local_ptrs_rel func cenv mid.scopes t` mp_tac >>
     qpat_assum `lookup_scopes id mid.scopes = _` mp_tac >>
     qpat_assum `FLOOKUP cenv.ce_vars id = _` mp_tac >>
     qpat_assum `lookup_var p t = _` mp_tac >>
     qpat_assum `entry'.type = _` mp_tac >>
     qpat_assum `type_memory_size tv = 32` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringStateRelDefsTheory.local_ptrs_rel_def] >> rpt strip_tac >>
     `type_memory_size entry'.type <= sz` by metis_tac[] >>
     gvs[type_memory_size_def] >> decide_tac) >>
  match_mp_tac (Q.INST [`H` |-> `H`, `ctx` |-> `ctx`, `func` |-> `func`,
    `cx` |-> `cx`, `es1` |-> `mid`, `s` |-> `t`, `id` |-> `id`,
    `t` |-> `u with vs_inst_idx := LENGTH sm.cs_current_insts + LENGTH (emitted_insts sm sb)`,
    `b` |-> `w2n (bp:256 word)`, `z` |-> `sz`, `n0` |-> `sz`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
      stmtSimDefsTheory.alloca_frame_local_store))) >>
  simp[] >> rpt conj_tac
  >- (qx_genl_tac [`x`, `wx`] >> strip_tac >>
      `not_fresh_at sm x` by
        (irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
      `lookup_var x t = SOME wx` by
        (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
         qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
           (qspecl_then [`x`, `wx`] mp_tac) >> simp[]) >>
      qpat_assum `!x a. not_fresh_at sm x /\ lookup_var x t = SOME a ==> _`
        (qspecl_then [`x`, `wx`] mp_tac) >> fs[lookup_var_def])
  >- (drule vyperLookupTheory.find_containing_scope_structure >>
      drule vyperLookupTheory.find_containing_scope_lookup >>
      simp[Abbr `ff`] >> rpt strip_tac >> gvs[] >>
      `id IN FDOM env''` by
        (qpat_assum `FLOOKUP env'' id = SOME entry'` mp_tac >>
         rpt (pop_assum kall_tac) >>
         Cases_on `id IN FDOM env''` >> simp[FLOOKUP_DEF]) >>
      fs[pred_setTheory.ABSORPTION])
  >- (rpt strip_tac >>
      `not_fresh_at sa q` by
        (qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
         qpat_assum `FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) z')` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
      `not_fresh_at sm q` by
        (irule loweringShapeDefsTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
      simp[lookup_var_def] >>
      irule (REWRITE_RULE [lookup_var_def]
        appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars) >>
      qexists_tac `emitted_insts sm sb` >> simp[] >>
      qpat_assum `compile_dynarray_append _ _ _ 32 32 _ _ _ _ _ sm = _` mp_tac >>
      qpat_assum `not_fresh_at sm q` mp_tac >> rpt (pop_assum kall_tac) >>
      simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
        contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
        fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> disch_then (SUBST1_TAC o SYM) >>
      simp_tac (srw_ss()) [emitted_insts_def] >>
      pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
      simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
      metis_tac[DECIDE ``n <= n+k``])
  >- (rpt strip_tac >>
      qpat_assum `state_frame u = _`
        (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
      simp_tac (srw_ss()) [stateFrameTheory.state_frame_def] >>
      disch_then SUBST1_TAC >>
      dep_rewrite.DEP_REWRITE_TAC
        [valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >> decide_tac)
QED

Finalise body_append_local_primitive_full

Theorem body_append_local_word_full:
  !cx id e.
    supported_full_word_type (expr_type e) /\
    (!s0 p s1. eval_target_place cx (NameTarget id) s0 = (INL p,s1) ==>
                  body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rpt strip_tac >>
  `is_word_type (expr_type e)` by fs[supported_full_word_type_def, is_word_type_def] >>
  metis_tac[body_append_local_primitive_full]
QED
