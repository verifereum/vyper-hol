(* Body composition for Append through a resolved local or nested place. *)
Theory bodyAppendResolvedCases
Ancestors
  bodyAppendResolvedPre bodyAugPlaceTarget bodySim stmtSimDefs
  stmtSimAppendResolved appendMemoryRel appendResolvedStorageRel appendMemoryPath
  stmtSimAppendStorageCompose appendStorageResolvedPath bodyAppendStorageAdapter
  exprSimPopNestedBase targetPlaceSim targetPlaceSimCases
  exprSimProps exprSimDefs exprSimSource exprSimHypsDefs exprLoweringProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext placeRelayoutGasCompose
  loweringStateRelDefs exprOperandVar loweringShapeDefs emitHelperProps
  fragGasSeq fragGasSeqAbort valueEncodingProps valueEncodingDefs
  fragGasMode fragGasPath fragExec stmtSimForced stmtLoweringMono
  vyperExprNoControl bodySimAugPlaceLoad bodySimAugPlaceLive stmtSimAugAssignPlaceMemory
  supportedExprTraverse supportedExprs targetSubscriptSplit
  stmtLowering exprLowering compileEnv supportedStmts supportedTargets supportedTypes
  vyperTyping vyperPlaceStatePreservation vyperValue
  vyperInterpreter vyperState venomState vyperTypeSystem vyperExprEffects list
Libs
  monadsyntax

Theorem body_append_resolved_case:
  !cx bt e.
    ~(?id. bt = TopLevelNameTarget id) /\
    (!s0 p s1. eval_target_place cx bt s0 = (INL p,s1) ==>
                  body_expr_ok cx e) /\
    body_base_target_ok cx bt ==>
    body_stmt_ok cx (Append bt e)
Proof
  rpt strip_tac >> rw[body_stmt_ok_def] >>
  drule_all body_append_resolved_pre >> strip_tac >>
  `target_sim ctx func cenv cx env bt es` by
    metis_tac[aug_place_body_target_sim] >>
  rw[stmt_frag_def, stmt_framed_frag_def] >>
  drule_all append_resolved_target_prefix >> strip_tac >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res`
     >- simp[target_place_res_ok_def] >>
     rename1 `eval_target_place cx bt _ = (INR ex,ee)` >>
     `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
     `eval_stmt cx (Append bt e) (es with gas_obs := gs) = (INR ex,ee)` by
       simp[Once evaluate_def, bind_def] >>
     `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
     gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]) >>
  drule_all target_place_sim >> strip_tac >>
  simp_tac bool_ss [Once evaluate_def] >>
  irule gas_outcome_bind_place >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ (eval_target_place _ _) _ _ _`)) >>
  simp[] >> conj_tac >- suspend "rhs" >>
  rpt strip_tac >> Cases_on `res` >> gvs[] >>
  rename1 `expr_exit (INR ex) rr` >>
  simp[stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume body_append_resolved_case[rhs]:
  rpt strip_tac >> gvs[] >>
  rename1 `gas_marked_exec F (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) mid (OK t)` >>
  `?gs. eval_target_place cx bt (es with gas_obs := gs) =
      (INL p,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [gas_marked_exec_def] >> strip_tac >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[]) >>
  rename1 `eval_target_place cx bt (es with gas_obs := gs) = _` >>
  `body_expr_ok cx e` by metis_tac[] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs) /\
   target_pre cenv cx env bt (es with gas_obs := gs)` by
    fs[target_pre_def] >>
  `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
    metis_tac[append_resolved_rhs_body_pre] >>
  `expr_sim ctx func cenv cx (expr_type e) e (mid with gas_obs := [])` by
    metis_tac[body_expr_ok_def] >>
  `supported_full_word_type (expr_type e)` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  `is_word_type (expr_type e)` by
    (qpat_x_assum `supported_full_word_type _` mp_tac >>
     rw[supported_full_word_type_def] >> simp[is_word_type_def]) >>
  `?bop loc. r = (bop,SOME loc,SOME (ValPT (ArrayT (expr_type e) (Dynamic cap))))` by
    (PairCases_on `r` >>
     qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[target_post_def, value_type_place_def] >> strip_tac >> gvs[] >>
     Cases_on `p` >> gvs[place_ptr_rel_def] >> metis_tac[]) >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >> suspend "code"
QED

Resume body_append_resolved_case[code]:
  drule_all append_resolved_word_code_parts >> strip_tac >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sm = (vop,sr)` >>
  `ci_mono sm sr` by
    (mp_tac (Q.SPECL [`cenv`, `expr_type e`, `e`, `sm`]
      (cj 2 ci_mono_compile_expr_sa)) >> simp[]) >>
  `ci_mono sr sb` by
    (mp_tac (Q.SPECL [`cenv`, `bop`, `vop`, `word_scale loc`,
      `elem_size_in_location cenv loc (expr_type e)`, `expr_type e`,
      `lowered_value_type cenv e`, `cap`, `T`, `load_opc_for loc`,
      `store_opc_for loc`, `sr`] ci_mono_compile_dynarray_append) >> simp[]) >>
  `fn_has_code sm sr func /\ fn_has_code sr sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`, `sr`, `vop`, `t`] mp_tac) >>
  impl_tac >- fs[target_post_def] >> strip_tac >>
  simp_tac bool_ss [GSYM bind_assoc] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule forced_then_outcome >> conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `\v ee u.
    expr_post ctx func cenv cx e (mid with gas_obs := []) sm sr t ee v vop u /\
    u.vs_current_bb = sr.cs_current_bb /\
    u.vs_inst_idx = LENGTH sr.cs_current_insts` >>
  conj_tac >- suspend "suffix" >>
  BETA_TAC >> first_assum ACCEPT_TAC
QED

Resume body_append_resolved_case[suffix]:
  rpt strip_tac >> gvs[] >>
  `gas_admissible
    (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
    (stmt_res_ok lctx) (mid with gas_obs := [])` by
    (qpat_assum `gas_admissible (eval_stmt cx (Append bt e)) _ es`
       (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV) o
        SIMP_RULE bool_ss [Once evaluate_def, GSYM bind_assoc]) >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     simp_tac (srw_ss()) [gas_admissible_def] >>
     map_every qx_gen_tac [`tailgs`, `out`, `srcend`] >> strip_tac >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `tailgs` assume_tac) >>
     qpat_assum `gas_admissible (monad_bind (eval_target_place cx bt) _) _ es`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then
       [`gas_explicit marks s0.vs_gas_readings ++ tailgs`, `out`, `srcend`] mp_tac) >>
     fs[bind_def]) >>
  `supported_pure_expr tops e` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  `~expr_has_effect e /\ supported_expr tops e` by
    metis_tac[supported_pure_expr_effect_free, supported_expr_def] >>
  `expr_body_pre cenv cx env e (mid with gas_obs := gs')` by fs[] >>
  `expr_sim_inv cenv cx env ee` by metis_tac[expr_body_pre_eval] >>
  `ee.scopes = mid.scopes` by
    (drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) aug_place_rhs_scopes) >> simp[]) >>
  `?bp. eval_operand bop t = SOME bp /\
    place_ptr_rel cenv cx t (PlaceR p) bp (SOME loc)
      (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    fs[target_post_def] >>
  `!l. bop <> Label l` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `eval_operand bop t' = SOME bp` by
    (Cases_on `bop` >> fs[eval_operand_def, target_post_def, expr_post_def]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
    lookup_var x t' = SOME w` by fs[expr_post_def] >>
  `place_ptr_rel cenv cx t' (PlaceR p) bp (SOME loc)
    (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    (Cases_on `p` >> fs[place_ptr_rel_def] >>
     metis_tac[local_ptrs_reserved_def]) >>
  Cases_on `p` >> gvs[place_ptr_rel_def]
  >~ [`append_place cx (MemoryPlace id path)`] >- suspend "memory" >>
  suspend "storage"
QED

Resume body_append_resolved_case[memory]:
  `?info. supported_target_info tops bindings bt = SOME info` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  `?entry old. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL old` by
    (drule_all aug_place_target_memory_live >> simp[] >> metis_tac[]) >>
  `tv0 = entry.type` by
    metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >> gvs[] >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    tv = ArrayTV etv (Dynamic cap)` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.state_well_typed_def] >>
     metis_tac[aug_place_lookup_typed]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic cap)) old` by
    metis_tac[evaluate_subscripts_type] >>
  `?vs. old = ArrayV (DynArrayV vs)` by
    (qpat_assum `value_has_type (ArrayTV etv (Dynamic cap)) old` mp_tac >>
     Cases_on `old` >> simp_tac (srw_ss()) [value_has_type_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >>
     simp_tac (srw_ss()) [value_has_type_def]) >> gvs[] >>
  rename1 `evaluate_subscripts entry.type entry.value path =
    INL (ArrayV (DynArrayV vs))` >>
  suspend "memory_ready"
QED

Resume body_append_resolved_case[memory_ready]:
  `stmt_state_rel ctx func cenv cx ee t'` by fs[expr_post_def] >>
  `place_ptr_rel cenv cx t' (PlaceR (MemoryPlace id path)) (b+n2w k)
    (SOME LocMemory) (Type (ArrayT (expr_type e) (Dynamic cap)))` by
    (simp[place_ptr_rel_def] >> metis_tac[]) >>
  `lookup_scopes id ee.scopes = SOME entry` by simp[] >>
  drule_all append_memory_array_layout >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `value_has_type etv v` by
    (`expr_body_pre cenv cx env e (mid with gas_obs := gs')` by fs[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def]) >>
  `safe_cast etv v = SOME v` by metis_tac[safe_cast_well_typed] >>
  `eval_operand vop t' = SOME (typed_val_to_w256 etv v)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ v vop t'`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [expr_post_def]) >>
     simp[expr_val_rel_def]) >>
  `type_memory_bytes cenv (expr_type e) = 32` by
    (qpat_x_assum `supported_full_word_type _` mp_tac >>
     rw[supported_full_word_type_def] >> simp[type_memory_bytes_def]) >>
  suspend "memory_layout"
QED

Resume body_append_resolved_case[memory_layout]:
  `compile_dynarray_append cenv bop vop 32 32 (expr_type e)
     (lowered_value_type cenv e) cap T MLOAD MSTORE sr = ((),sb)` by
    fs[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       load_opc_for_def, store_opc_for_def] >>
  `!x. vop = Var x ==> not_fresh_at sr x` by
    metis_tac[compile_lower_value_var] >>
  `!x. bop = Var x ==> not_fresh_at sr x` by
    (fs[target_post_def, ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. bop = Var x \/ vop = Var x ==> not_fresh_at sr x` by metis_tac[] >>
  drule append_memory_word_footprint >> strip_tac >>
  `alloca_room ctx func t'` by fs[stmt_state_rel_def, state_rel_def] >>
  `t'.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b+n2w k) + 32*(1+cap) <= dimword (:256)` by decide_tac >>
  drule_all append_memory_word_run_reserved >> strip_tac >>
  suspend "memory_runs"
QED

Resume body_append_resolved_case[memory_runs]:
  `LENGTH vs <= cap` by
    (qpat_assum `value_has_type (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV vs))` mp_tac >>
     simp_tac bool_ss [Once value_has_type_def] >> simp[]) >>
  `mload (w2n (b+n2w k)) t' = n2w (LENGTH vs)` by
    (qpat_assum `val_in_memory (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV vs)) _ t'.vs_memory` mp_tac >>
     simp_tac bool_ss [Once valueEncodingDefsTheory.val_in_memory_def] >>
     simp[GSYM mem_word_at_eq_mload]) >>
  `w2n (mload (w2n (b+n2w k)) t') = LENGTH vs` by
    (simp[] >> `LENGTH vs < dimword (:256)` by decide_tac >> simp[]) >>
  `?bb. lookup_block t'.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sr sb) (DROP t'.vs_inst_idx bb.bb_instructions) /\
    t'.vs_inst_idx + LENGTH (emitted_insts sr sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sr sb)` by
    (qpat_x_assum `EVERY _ (emitted_insts sr sb)` mp_tac >>
     match_mp_tac listTheory.EVERY_MONOTONIC >>
     simp_tac (srw_ss()) [MEM, DISJ_IMP_THM, FORALL_AND_THM,
       venomInstTheory.is_terminator_def]) >>
  Cases_on `LENGTH vs < cap` >- suspend "memory_store" >>
  suspend "memory_full"
QED

Resume body_append_resolved_case[memory_full]:
  `cap <= w2n (mload (w2n (b+n2w k)) t')` by decide_tac >>
  `?abrt tu. run_inst_seq (emitted_insts sr sb) t' = Abort abrt tu` by
    (qpat_assum `cap <= w2n (mload _ t') ==> _` mp_tac >> simp[]) >>
  qspecl_then [`emitted_insts sr sb`, `t'`, `tu`, `abrt`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_abort_zero_path >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "append overflow"))`, `ee`,
    `Abort abrt (tu with vs_inst_idx := j)`] >>
  simp[append_place_def, place_type_value_def, read_place_def,
       get_scopes_def, lift_option_type_def, bind_def, return_def, lift_sum_def,
       read_memory_path_def, vyperValueOperationTheory.append_element_def,
       compatible_bound_def, raise_def, stmt_exit_def, expr_exit_def, exit_result_def]
QED

Resume body_append_resolved_case[memory_store]:
  qabbrev_tac `nv = ArrayV (DynArrayV (vs ++ [v]))` >>
  `SUC (LENGTH vs) <= cap` by decide_tac >>
  `append_place cx (MemoryPlace id path) v ee =
    write_place cx (MemoryPlace id path) nv ee` by
    simp[append_place_def, place_type_value_def, read_place_def, get_scopes_def,
      lift_option_type_def, bind_def, return_def, lift_sum_def,
      read_memory_path_def, vyperValueOperationTheory.append_element_def,
      compatible_bound_def, SNOC_APPEND, Abbr `nv`] >>
  Cases_on `write_place cx (MemoryPlace id path) nv ee` >>
  rename1 `write_place cx (MemoryPlace id path) nv ee = (wres,ff)` >>
  `bind (bind (eval_expr cx e) (read_result cx))
     (append_place cx (MemoryPlace id path)) (mid with gas_obs := gs') =
       (wres,ff)` by
    fs[bind_def] >>
  `stmt_res_ok lctx wres` by metis_tac[gas_admissible_result] >>
  `lookup_scopes id ee.scopes = SOME entry` by simp[] >>
  `wres = INL ()` by metis_tac[aug_place_memory_write_success] >>
  qpat_x_assum `wres = INL ()` SUBST_ALL_TAC >>
  `value_has_type (ArrayTV etv (Dynamic cap)) nv` by
    (qpat_assum `value_has_type (ArrayTV etv (Dynamic cap))
      (ArrayV (DynArrayV vs))` mp_tac >>
     simp_tac bool_ss [Once value_has_type_def, all_have_type_EVERY] >> strip_tac >>
     simp[Abbr `nv`, Once value_has_type_def, all_have_type_EVERY, EVERY_APPEND,
       GSYM arithmeticTheory.ADD1]) >>
  suspend "memory_write"
QED

Resume body_append_resolved_case[memory_write]:
  `supported_full_word_type (expr_type e)` by
    (Cases_on `bt` >> fs[Once supported_stmt_def]) >>
  `val_in_memory etv v (w2n (b+n2w k)+32*(1+LENGTH vs))
    (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
      (typed_val_to_w256 etv v) t').vs_memory` by
    (qpat_assum `value_has_type etv v` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME etv` mp_tac >>
     qpat_assum `supported_full_word_type (expr_type e)` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >>
     rw[supported_full_word_type_def] >>
     gvs[vyperValueTheory.evaluate_type_def] >> Cases_on `v` >>
     gvs[value_has_type_def, val_in_memory_def, valueEncodingTheory.typed_val_to_w256_def,
       mstore_mem_word_at_same]) >>
  `!entry t0. lookup_scopes id ee.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (map_every qx_gen_tac [`newentry`, `newty`] >> strip_tac >>
     qpat_assum `expr_sim_inv cenv cx env ee` mp_tac >>
     qpat_assum `lookup_scopes id ee.scopes = SOME newentry` mp_tac >>
     qpat_assum `cenv.ce_var_type id = SOME newty` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >>
     metis_tac[aug_place_entry_type_agrees]) >>
  qunabbrev_tac `nv` >>
  `stmt_state_rel ctx func cenv cx ff
    (mstore (w2n (b+n2w k)) (n2w (LENGTH vs+1))
      (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
        (typed_val_to_w256 etv v) t'))` by
    (irule (Q.INST [`env` |-> `env`, `id` |-> `id`, `path` |-> `path`,
       `dty` |-> `ArrayT (expr_type e) (Dynamic cap)`, `tv` |-> `etv`,
       `cap` |-> `cap`, `vs` |-> `vs`, `v` |-> `v`] append_memory_word_state) >>
     qexistsl_tac [`cap`, `e`, `env`, `ee`, `etv`, `id`, `path`, `v`] >>
     simp[]) >>
  `?u. run_inst_seq (emitted_insts sr sb) t' = OK u /\
    state_frame u = state_frame
      (mstore (w2n (b+n2w k)) (n2w (LENGTH vs+1))
        (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
          (typed_val_to_w256 etv v) t')) /\
    (!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==>
       lookup_var x u = SOME a)` by
    (qpat_assum `!len. len = w2n (mload _ t') /\ len < cap ==> _`
       (qspec_then `LENGTH vs` mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `!z. lookup_var z
    (mstore (w2n (b+n2w k)) (n2w (LENGTH vs+1))
      (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
        (typed_val_to_w256 etv v) t')) = lookup_var z t'` by
    simp_tac (srw_ss()) [lookup_var_def, mstore_def] >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (irule stmt_state_rel_reserved_frame >>
     qexistsl_tac [`mstore (w2n (b+n2w k)) (n2w (LENGTH vs+1))
       (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
         (typed_val_to_w256 etv v) t')`, `sr`] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  suspend "memory_frame"
QED

Resume body_append_resolved_case[memory_frame]:
  `mid.scopes = es.scopes` by
    (drule_all aug_place_target_scopes >> simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[] >>
  `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
    (drule_all target_post_alloca_frame >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [target_post_def]) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  `alloca_frame cenv (mid with gas_obs := []) sm t cenv ee t'` by
    (drule_all expr_post_alloca_frame >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee t'` by
    (irule alloca_frame_trans >>
     qexistsl_tac [`cenv`, `mid with gas_obs := []`, `t`, `sm`] >>
     simp[] >> fs[ci_mono_def, target_post_def]) >>
  qabbrev_tac `out = mstore (w2n (b+n2w k)) (n2w (LENGTH vs+1))
    (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
      (typed_val_to_w256 etv v) t')` >>
  `local_region cenv ee.scopes t' id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes t'` by
    (qpat_assum `stmt_state_rel ctx func cenv cx ee t'`
       (mp_tac o CONJUNCT1 o CONJUNCT1 o
        REWRITE_RULE [stmt_state_rel_def, state_rel_def]) >> simp[]) >>
  `type_memory_size entry.type <= sz /\
   w2n b + sz <= t'.vs_alloca_next` by
    (qpat_assum `local_ptrs_rel func cenv ee.scopes t'`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac) >> simp[]) >>
  `w2n (b+n2w k) = w2n b+k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >>
     gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  suspend "memory_alloca"
QED

Resume body_append_resolved_case[memory_alloca]:
  `w2n b <= w2n (b+n2w k) /\
   w2n (b+n2w k)+32*(1+LENGTH vs)+32 <= w2n b+sz` by
    (qpat_assum `type_memory_size etv = 32` (fn szth =>
       qpat_assum `k + type_memory_size (ArrayTV etv (Dynamic cap)) <= _`
         (mp_tac o REWRITE_RULE [valueEncodingTheory.type_memory_size_def, szth])) >>
     strip_tac >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `alloca_frame cenv es sa s0 cenv ff out` by
    (irule alloca_frame_region_write >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[] >>
     rpt strip_tac >> qunabbrev_tac `out` >>
     irule EQ_TRANS >>
     qexists_tac `mem_bytes_at ad len
       (mstore (w2n (b+n2w k)+32*(1+LENGTH vs))
         (typed_val_to_w256 etv v) t').vs_memory` >> conj_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `u.vs_memory = out.vs_memory /\ u.vs_allocas = t'.vs_allocas /\
   ~u.vs_halted /\ u.vs_current_bb = t'.vs_current_bb` by
    (qpat_assum `state_frame u = state_frame out`
       (mp_tac o Q.AP_TERM
         `\s. (s.vs_memory, s.vs_allocas, s.vs_halted, s.vs_current_bb)`) >>
     simp_tac (srw_ss()) [stateFrameTheory.state_frame_def] >> strip_tac >>
     asm_simp_tac (srw_ss()) [Abbr `out`, mstore_def, LET_THM]) >>
  `local_ptrs_rel func cenv ff.scopes out` by
    (qpat_assum `stmt_state_rel ctx func cenv cx ff out`
       (mp_tac o CONJUNCT1 o CONJUNCT1 o
        REWRITE_RULE [stmt_state_rel_def, state_rel_def]) >> simp[]) >>
  `!name ent q z. lookup_scopes name ff.scopes = SOME ent /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) z) ==>
    lookup_var q u = lookup_var q out` by
    (map_every qx_gen_tac [`lname`, `lent`, `lq`, `lsz`] >> strip_tac >>
     qpat_assum `local_ptrs_rel func cenv ff.scopes out`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`lname`, `lent`, `lq`, `lsz`] mp_tac) >>
     impl_tac >- simp[] >> disch_then (qx_choose_then `lw` strip_assume_tac) >>
     `not_fresh_at sr lq` by
       (qpat_assum `local_ptrs_reserved cenv sr`
          (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
        disch_then (qspecl_then [`lname`, `lname`, `lq`, `lsz`, `lsz`] mp_tac) >> simp[]) >>
     `lookup_var lq t' = SOME lw` by metis_tac[] >>
     qpat_assum `!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==> _`
       (qspecl_then [`lq`, `lw`] mp_tac) >> simp[]) >>
  `!name base sz'. local_region cenv ff.scopes u name base sz' <=>
     local_region cenv ff.scopes out name base sz'` by
    (rpt gen_tac >> irule local_region_lookup_cong >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv ff u` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv ff out` mp_tac >>
     simp_tac bool_ss [alloca_frame_def] >> asm_simp_tac bool_ss []) >>
  suspend "memory_path"
QED

Resume body_append_resolved_case[memory_path]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sr sb)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> GAS /\ _) _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> simp_tac std_ss [EVERY_MEM] >> metis_tac[]) >>
  qspecl_then [`emitted_insts sr sb`, `t'`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- simp[] >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sr sb)) = 0` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> GAS /\ _) _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >>
     simp_tac std_ss [LENGTH_NIL, FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `gas_marked_path F ctx func t' 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_assum `t'.vs_inst_idx + LENGTH (emitted_insts sr sb) = _` (fn pcth =>
       qpat_assum `LENGTH (FILTER _ (emitted_insts sr sb)) = 0` (fn gasth =>
         qpat_assum `gas_path ctx func t' _ (OK _)`
           (mp_tac o PURE_REWRITE_RULE [pcth, gasth]))) >>
     simp_tac bool_ss [gas_marked_path_def]) >>
  `lookup_scopes id es.scopes = SOME entry` by
    (qpat_assum `lookup_scopes id ee.scopes = SOME entry` mp_tac >>
     qpat_assum `ee.scopes = mid.scopes` mp_tac >>
     qpat_assum `mid.scopes = es.scopes` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> metis_tac[]) >>
  `!tail. append_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
    (INL (),ff with gas_obs := tail)` by
    (gen_tac >>
     `write_place cx (MemoryPlace id path) (ArrayV (DynArrayV (vs ++ [v])))
        (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
       metis_tac[aug_place_memory_write_gas_obs] >>
     simp[append_place_def, place_type_value_def, read_place_def,
       get_scopes_def, lift_option_type_def, bind_def, return_def, lift_sum_def,
       read_memory_path_def, vyperValueOperationTheory.append_element_def,
       compatible_bound_def, SNOC_APPEND]) >>
  `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
     lookup_var z u = SOME a` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [target_post_def] th), 5))) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [expr_post_def] th), 4))) >>
     qpat_assum `!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==> _` mp_tac >>
     qpat_assum `ci_mono sa sm` mp_tac >> qpat_assum `ci_mono sm sr` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> rw[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==>
     FLOOKUP u.vs_allocas aid = SOME rb` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [target_post_def] th), 6))) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [expr_post_def] th), 5))) >>
     qpat_assum `u.vs_allocas = t'.vs_allocas` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv (ff with gas_obs := [])
    (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv ff u` mp_tac >>
     simp_tac (srw_ss()) [alloca_frame_def, local_region_def, lookup_var_def]) >>
  qexistsl_tac [`INL ()`, `ff`, `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[] >> disj1_tac >> irule aug_place_normal_post >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs, stmt_state_rel_inst_idx,
    lookup_var_def] >>
  qpat_assum `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==> _`
    (mp_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
  qpat_assum `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==> _` mp_tac >>
  qpat_assum `u.vs_allocas = t'.vs_allocas` mp_tac >>
  qpat_assum `same_blocks sr sb` (mp_tac o REWRITE_RULE [same_blocks_def]) >>
  rpt (pop_assum (K ALL_TAC)) >> metis_tac[]
QED

Resume body_append_resolved_case[storage]:
  rename1 `append_place cx (StoragePlace tr bp stv) v` >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    stv = ArrayTV etv (Dynamic cap)` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `stmt_state_rel ctx func cenv cx ee t'` by fs[expr_post_def] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `storage_place_region cx (StoragePlace tr bp (ArrayTV etv (Dynamic cap)))` by
    metis_tac[vyperStoragePlaceProvenanceTheory.eval_target_place_region] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  `0 < type_slot_size (ArrayTV etv (Dynamic cap))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  `storage_read_live cx tr (get_storage cx ee tr) bp (ArrayTV etv (Dynamic cap))` by
    (irule accountsRelPropsTheory.storage_place_region_read_live >> simp[]) >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  `type_slot_size etv = 1` by
    (qpat_x_assum `supported_full_word_type (expr_type e)` mp_tac >>
     rw[supported_full_word_type_def] >>
     fs[vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def]) >>
  `cap < dimword (:256)` by
    (qpat_assum `type_slot_size etv = 1` (fn szth =>
       qpat_assum `w2n bp + type_slot_size (ArrayTV etv (Dynamic cap)) <= _`
         (mp_tac o REWRITE_RULE [vyperValueTheory.type_slot_size_def, szth])) >>
     decide_tac) >>
  `expr_body_pre cenv cx env e (mid with gas_obs := gs')` by fs[] >>
  `encode_value etv v = SOME [(0,typed_val_to_w256 etv v)]` by
    (drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) body_append_word_encoding) >> simp[]) >>
  `eval_operand vop t' = SOME (typed_val_to_w256 etv v)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ v vop t'`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [expr_post_def]) >>
     simp[expr_val_rel_def]) >>
  `type_memory_bytes cenv (expr_type e) = 32` by
    (qpat_x_assum `supported_full_word_type (expr_type e)` mp_tac >>
     rw[supported_full_word_type_def] >> simp[type_memory_bytes_def]) >>
  `compile_dynarray_append cenv bop vop 1 1 (expr_type e)
    (lowered_value_type cenv e) cap T (if tr then TLOAD else SLOAD)
      (if tr then TSTORE else SSTORE) sr = ((),sb)` by
    (Cases_on `tr` >> fs[slot_loc_def, word_scale_def, elem_size_in_location_def,
      is_slot_addressed_def, load_opc_for_def, store_opc_for_def]) >>
  `~cx.txn.is_static /\ ~t'.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!x. vop = Var x ==> not_fresh_at sr x` by
    metis_tac[compile_lower_value_var] >>
  `!x. bop = Var x ==> not_fresh_at sr x` by
    (fs[target_post_def, ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. bop = Var x \/ vop = Var x ==> not_fresh_at sr x` by metis_tac[] >>
  drule_all append_storage_word_run_reserved >> strip_tac >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  suspend "storage_runs"
QED

Resume body_append_resolved_case[storage_runs]:
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sr sb)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> GAS /\ _) _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> simp_tac std_ss [EVERY_MEM] >> metis_tac[]) >>
  Cases_on `w2n (lookup_storage bp (get_storage cx ee tr)) < cap`
  >- suspend "storage_store" >> suspend "storage_full"
QED

Resume body_append_resolved_case[storage_full]:
  `cap <= w2n (lookup_storage bp (get_storage cx ee tr))` by decide_tac >>
  `cap <= w2n (if tr then tload bp t' else sload bp t')` by
    (qpat_assum `(if tr then tload bp t' else sload bp t') = _` mp_tac >>
     qpat_assum `cap <= w2n (lookup_storage bp (get_storage cx ee tr))` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> simp[]) >>
  `?abrt tu. run_inst_seq (emitted_insts sr sb) t' = Abort abrt tu` by
    (qpat_assum `cap <= w2n (if tr then tload bp t' else sload bp t') ==> _`
       mp_tac >> simp[]) >>
  qspecl_then [`emitted_insts sr sb`, `t'`, `tu`, `abrt`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_abort_zero_path >>
  impl_tac >- simp[] >> strip_tac >>
  `!tail. append_place cx (StoragePlace tr bp (ArrayTV etv (Dynamic cap))) v
     (ee with gas_obs := tail) =
     (INR (Error (RuntimeError "append full storage array")),ee with gas_obs := tail)` by
    (gen_tac >> irule stmtSimAppendStorageTheory.append_storage_full >>
     pure_rewrite_tac [get_storage_gas_obs] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`INR (Error (RuntimeError "append full storage array"))`, `ee`,
    `Abort abrt (tu with vs_inst_idx := j)`] >>
  simp[stmt_exit_def, expr_exit_def, exit_result_def]
QED

Resume body_append_resolved_case[storage_store]:
  qabbrev_tac `len = w2n (lookup_storage bp (get_storage cx ee tr))` >>
  `len < cap /\ len = w2n (if tr then tload bp t' else sload bp t')` by
    (qunabbrev_tac `len` >>
     qpat_assum `(if tr then tload bp t' else sload bp t') = _` mp_tac >>
     qpat_assum `w2n (lookup_storage bp (get_storage cx ee tr)) < cap` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> simp[]) >>
  qabbrev_tac `ff = set_storage cx ee tr
    (update_storage bp (n2w (len+1))
      (update_storage (bp+n2w (1+len)) (typed_val_to_w256 etv v)
        (get_storage cx ee tr)))` >>
  `len = w2n (lookup_storage bp (get_storage cx ee tr))` by simp[Abbr `len`] >>
  `append_place cx (StoragePlace tr bp (ArrayTV etv (Dynamic cap))) v ee =
     (INL (),ff)` by
    (qunabbrev_tac `ff` >>
     drule_all stmtSimAppendStorageTheory.append_storage_word_success >>
     rpt (pop_assum (K ALL_TAC)) >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.set_storage_def]) >>
  suspend "storage_state"
QED

Resume body_append_resolved_case[storage_state]:
  `stmt_state_rel ctx func cenv cx ff
    (if tr then tstore bp (n2w (len+1))
    (tstore (bp+n2w (1+len)) (typed_val_to_w256 etv v) t')
    else sstore bp (n2w (len+1))
      (sstore (bp+n2w (1+len)) (typed_val_to_w256 etv v) t'))` by
    (qunabbrev_tac `ff` >>
     drule_all stmt_state_rel_append_resolved_storage_updates >>
     disch_then (qspec_then `typed_val_to_w256 etv v` ACCEPT_TAC)) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx ff out` >>
  `?u. run_inst_seq (emitted_insts sr sb) t' = OK u /\
    state_frame u = state_frame out /\
    (!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==>
       lookup_var x u = SOME a)` by
    (qpat_assum `!len. len = w2n (if tr then tload bp t' else sload bp t') /\
       len < cap ==> _` (qspec_then `len` mp_tac) >>
     simp_tac bool_ss [Abbr `out`] >> impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `len = w2n (if tr then tload bp t' else sload bp t')` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> Cases_on `tr` >> simp[]) >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> conj_tac
     >- (qpat_assum `ci_mono sm sr` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
         rpt (pop_assum (K ALL_TAC)) >> simp[]) >> first_assum ACCEPT_TAC) >>
  `!z. lookup_var z out = lookup_var z t'` by
    (Cases_on `tr` >>
     simp_tac (srw_ss()) [Abbr `out`, lookup_var_def, sstore_def, tstore_def, LET_THM]) >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (irule stmt_state_rel_reserved_frame >> qexistsl_tac [`out`, `sr`] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `u.vs_memory = t'.vs_memory /\ u.vs_allocas = t'.vs_allocas /\
   ~u.vs_halted /\ u.vs_current_bb = t'.vs_current_bb` by
    (qunabbrev_tac `out` >> qpat_assum `state_frame u = _`
       (mp_tac o Q.AP_TERM
         `\s. (s.vs_memory, s.vs_allocas, s.vs_halted, s.vs_current_bb)`) >>
     qpat_assum `~t'.vs_halted` mp_tac >> rpt (pop_assum (K ALL_TAC)) >>
     Cases_on `tr` >>
     simp[stateFrameTheory.state_frame_def, sstore_def, tstore_def, LET_THM]) >>
  `ff.scopes = ee.scopes` by
    (qunabbrev_tac `ff` >> rpt (pop_assum (K ALL_TAC)) >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.set_storage_def]) >>
  suspend "storage_frame"
QED

Resume body_append_resolved_case[storage_frame]:
  `?info. supported_target_info tops bindings bt = SOME info` by
    (qpat_assum `supported_stmt tops bindings (Append bt e)` mp_tac >>
     qpat_assum `!id. bt <> TopLevelNameTarget id` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> rpt strip_tac >>
     Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  `mid.scopes = es.scopes` by
    (drule_all aug_place_target_scopes >> simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[] >>
  `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
    (drule_all target_post_alloca_frame >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [target_post_def]) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  `alloca_frame cenv (mid with gas_obs := []) sm t cenv ee t'` by
    (drule_all expr_post_alloca_frame >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee t'` by
    (irule alloca_frame_trans >>
     qexistsl_tac [`cenv`, `mid with gas_obs := []`, `t`, `sm`] >>
     qpat_assum `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` mp_tac >>
     qpat_assum `alloca_frame cenv (mid with gas_obs := []) sm t cenv ee t'` mp_tac >>
     qpat_assum `ci_mono sa sm` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth
         (CONJUNCTS (PURE_REWRITE_RULE [target_post_def] th), 6))) >>
     rpt (pop_assum (K ALL_TAC)) >> rpt strip_tac >> metis_tac[]) >>
  `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==>
     FLOOKUP t'.vs_allocas aid = SOME rb` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [target_post_def] th), 6))) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [expr_post_def] th), 5))) >>
     rpt (pop_assum (K ALL_TAC)) >> metis_tac[]) >>
  `alloca_frame cenv ee sr t' cenv ff u` by
    (qpat_assum `stmt_state_rel ctx func cenv cx ee t'` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sr` mp_tac >>
     qpat_assum `ff.scopes = ee.scopes` mp_tac >>
     qpat_assum `u.vs_memory = t'.vs_memory` mp_tac >>
     qpat_assum `!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==> _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> rpt strip_tac >>
     irule (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `cx` |-> `cx`]
       alloca_frame_of_mem_frame) >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv ff u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`, `ee`, `t'`, `sr`] >>
     qpat_assum `alloca_frame cenv es sa s0 cenv ee t'` mp_tac >>
     qpat_assum `alloca_frame cenv ee sr t' cenv ff u` mp_tac >>
     qpat_assum `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==>
       FLOOKUP t'.vs_allocas aid = SOME rb` mp_tac >>
     qpat_assum `ci_mono sa sm` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono sm sr` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     rpt (pop_assum (K ALL_TAC)) >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "storage_path"
QED

Resume body_append_resolved_case[storage_path]:
  `~block_is_terminated sb` by
    (drule append_storage_word_suffix_open >> disch_then ACCEPT_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sr sb)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> GAS /\ _) _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> simp_tac std_ss [EVERY_MEM] >> metis_tac[]) >>
  qspecl_then [`emitted_insts sr sb`, `t'`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- simp[] >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sr sb)) = 0` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> GAS /\ _) _` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >>
     simp_tac std_ss [LENGTH_NIL, FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `gas_marked_path F ctx func t' 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_assum `t'.vs_inst_idx + LENGTH (emitted_insts sr sb) = _` (fn pcth =>
       qpat_assum `LENGTH (FILTER _ (emitted_insts sr sb)) = 0` (fn gasth =>
         qpat_assum `gas_path ctx func t' _ (OK _)`
           (mp_tac o PURE_REWRITE_RULE [pcth, gasth]))) >>
     simp_tac bool_ss [gas_marked_path_def]) >>
  `!tail. append_place cx (StoragePlace tr bp (ArrayTV etv (Dynamic cap))) v
     (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
    (gen_tac >> drule append_storage_place_gas_obs >>
     disch_then (qspec_then `tail` ACCEPT_TAC)) >>
  `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
     lookup_var z u = SOME a` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [target_post_def] th), 5))) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o (fn th => List.nth (CONJUNCTS (PURE_REWRITE_RULE [expr_post_def] th), 4))) >>
     qpat_assum `!x a. not_fresh_at sr x /\ lookup_var x t' = SOME a ==> _` mp_tac >>
     qpat_assum `ci_mono sa sm` mp_tac >> qpat_assum `ci_mono sm sr` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> rw[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==>
     FLOOKUP u.vs_allocas aid = SOME rb` by
    (qpat_assum `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==>
       FLOOKUP t'.vs_allocas aid = SOME rb` mp_tac >>
     qpat_assum `u.vs_allocas = t'.vs_allocas` mp_tac >>
     rpt (pop_assum (K ALL_TAC)) >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv (ff with gas_obs := [])
    (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv ff u` mp_tac >>
     simp_tac (srw_ss()) [alloca_frame_def, local_region_def, lookup_var_def]) >>
  qexistsl_tac [`INL ()`, `ff`, `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[] >> disj1_tac >> irule aug_place_normal_post >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs, stmt_state_rel_inst_idx,
    lookup_var_def] >>
  qpat_assum `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==> _`
    (mp_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
  qpat_assum `!aid rb. FLOOKUP s0.vs_allocas aid = SOME rb ==> _` mp_tac >>
  qpat_assum `u.vs_allocas = t'.vs_allocas` mp_tac >>
  qpat_assum `same_blocks sr sb` (mp_tac o REWRITE_RULE [same_blocks_def]) >>
  qpat_assum `~block_is_terminated sb` mp_tac >>
  rpt (pop_assum (K ALL_TAC)) >> metis_tac[]
QED

Finalise body_append_resolved_case

Theorem body_append_local_case:
  !cx id e.
    (!s0 p s1. eval_target_place cx (NameTarget id) s0 = (INL p,s1) ==>
                body_expr_ok cx e) ==>
    body_stmt_ok cx (Append (NameTarget id) e)
Proof
  rpt strip_tac >> irule body_append_resolved_case >>
  simp[body_base_target_ok_def] >> first_assum ACCEPT_TAC
QED

Theorem body_append_subscript_case:
  !cx bt key e.
    (!s0 p s1. eval_target_place cx (SubscriptTarget bt key) s0 = (INL p,s1) ==>
                body_expr_ok cx e) /\
    body_base_target_ok cx (SubscriptTarget bt key) ==>
    body_stmt_ok cx (Append (SubscriptTarget bt key) e)
Proof
  rpt strip_tac >> irule body_append_resolved_case >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_append_attribute_case:
  !cx bt field e.
    (!s0 p s1. eval_target_place cx (AttributeTarget bt field) s0 = (INL p,s1) ==>
                body_expr_ok cx e) /\
    body_base_target_ok cx bt ==>
    body_stmt_ok cx (Append (AttributeTarget bt field) e)
Proof
  rpt strip_tac >> irule body_append_resolved_case >>
  simp[body_base_target_ok_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

