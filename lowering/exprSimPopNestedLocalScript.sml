(*
 * Pop on a nested target: pop_nested_local_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedLocal
Ancestors
  exprSimPopNestedBase exprSimPopNestedLocalPopped
  exprSimPopNestedLocalPost exprSimPopNestedLocalRun exprSimCalldataSlice
  exprSimPopNestedLocalSuffix vyperEvalExprPreservesScopesDom
  exprSimPopNestedLocalSource exprSimPopNestedLocalHandoff gasOutcome gasSummary gasSummaryCompose gasExemptCert
  loweringPosts bodySim exprSimHypsDefs stmtSimProps
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation vyperLookup

(* Pop on an array inside a memory local, the local itself included
   (x.pop(), x.a.pop(), x[i].pop()), when every evaluation of the target
   leaves its place live in the local's value or unreadable.  The run is
   compile_pop_name_sim's at the target's pointer: the pop stores the
   array's new length word inside the local's region, which locals_kept
   exempts (dynarray_len_at), and the result is the element's pointer,
   read back through the popped history. *)
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >> PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  Cases_on `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm r` by metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  qpat_x_assum `pop_target_frag _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[pop_target_frag_def] >> disch_then drule_all >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_local_sim[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `tr0`] strip_assume_tac) >>
  gvs[] >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `tr0`] >> simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume pop_nested_local_sim[normal]:
  Cases_on `?path entry err v. p = MemoryPlace id path /\
              lookup_scopes id tend.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INR err /\
              read_popped entry.type path entry.popped = SOME v`
  >- (goalStack.print_tac "PROBE" >> cheat) >>
  `!path entry err. p = MemoryPlace id path /\
     lookup_scopes id tend.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INR err ==>
     read_popped entry.type path entry.popped = NONE` by
    (rpt strip_tac >> Cases_on `read_popped entry.type path entry.popped` >>
     fs[] >> metis_tac[]) >>
  `place_readable cx (tend with gas_obs := []) (PlaceR p)` by
    fs[target_post_def] >>
  drule_all pop_counted_source_handoff >> strip_tac >> gvs[] >>
  `lookup_scopes id (tend with gas_obs := []).scopes = SOME entry` by simp[] >>
  drule_all memory_target_encoding_handoff >> strip_tac >>
  gvs[value_type_place_def, Abbr `lc`, Abbr `ws`, Abbr `esz`,
      word_scale_def, elem_size_in_location_def, is_slot_addressed_def] >>
  `tv = ArrayTV etv (Dynamic n')` by
    (drule mem_path_offset_sound >> simp[]) >> gvs[] >>
  `val_wf (ArrayTV etv (Dynamic n')) (ArrayV (DynArrayV vs)) /\
   val_in_memory (ArrayTV etv (Dynamic n')) (ArrayV (DynArrayV vs))
     (w2n b + k) t.vs_memory` by
    (drule_all exprSimPopNestedLocalMemoryTheory.val_in_memory_mutable_path >> simp[]) >>
  `mload (w2n (b + n2w k)) t = n2w (LENGTH vs)` by
    (fs[valueEncodingTheory.val_in_memory_def] >>
     gvs[venomStateTheory.mload_def, valueEncodingTheory.mem_word_at_def,
         arithmeticTheory.ADD_COMM]) >>
  `MAP FDOM es.scopes = MAP FDOM tend.scopes` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >> drule eval_target_place_preserves_scopes_dom >> simp[]) >>
  drule_all pop_array_element_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `popped_keys_indexed tend.scopes` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `expr_sim_inv _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >>
     drule stmtPoppedKeysTheory.eval_target_place_popped_keys_indexed >>
     fs[expr_sim_inv_def]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `target_root _ = _` kall_tac >>
  qpat_x_assum `type_place_target _ _ = _` kall_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `place_readable _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_target_place _ _) _ _` kall_tac >>
  drule memory_pop_shape >> strip_tac >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[gasSummaryTheory.gas_marked_exec_def,
          fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  Cases_on `vs = []`
  >- suspend "empty" >>
  suspend "nonempty"
QED

Resume pop_nested_local_sim[empty]:
  qpat_x_assum `vs = []` SUBST_ALL_TAC >>
  `mload (w2n (b + n2w k)) t = 0w` by simp[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[listTheory.ALL_DISTINCT] >>
  drule_all memory_pop_run_empty >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_memory_bytes cenv ann`] strip_assume_tac) >>
  drule_all memory_pop_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `find_containing_scope id (tend with gas_obs := []).scopes =
     SOME (pre,env',entry,rest)` by simp[] >>
  drule_all memory_pop_empty_exec >>
  disch_then (qspec_then `cx` assume_tac) >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty memory array"))`,
    `tend with gas_obs := []`, `Abort a (t' with vs_inst_idx := j)`] >>
  conj_tac
  >- (once_rewrite_tac[GSYM APPEND_NIL] >>
      irule gas_marked_exec_bind_normal >> goal_assum drule >> simp[]) >>
  simp[expr_exit_def, exit_result_def]
QED

Resume pop_nested_local_sim[nonempty]:
  `well_formed_type_value (ArrayTV etv (Dynamic n'))` by
    metis_tac[vyperPlaceStatePreservationTheory.subscripts_type_well_formed] >>
  `LENGTH vs < dimword (:256)` by
    (fs[valueEncodingTheory.val_wf_def, vyperTypingTheory.well_formed_type_value_def]) >>
  `mload (w2n (b + n2w k)) t <> 0w` by
    (simp[] >> simp[wordsTheory.n2w_11] >> Cases_on `vs` >> gvs[]) >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[listTheory.ALL_DISTINCT] >>
  `EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6]` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all memory_pop_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_memory_bytes cenv ann`] strip_assume_tac) >>
  drule_all memory_pop_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all exprSimPopNestedLocalPropsTheory.pop_memory_live_transition >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  qpat_x_assum `let t = _ in _` (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `pop_place cx _ tend = (_,fin)` >>
  `find_containing_scope id (tend with gas_obs := []).scopes =
     SOME (pre,env',entry,rest)` by simp[] >>
  drule_all memory_pop_live_exec >>
  disch_then (qspec_then `cx` mp_tac) >>
  simp[Abbr `fin`] >> strip_tac >>
  `k + 32 + (LENGTH vs - 1) * type_memory_size etv <= sz` by
    (`LENGTH vs <= n'` by fs[valueEncodingTheory.val_wf_def] >>
     ` (LENGTH vs - 1) * type_memory_size etv <= n' * type_memory_size etv` by
       (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `(LENGTH vs - 1) * _ <= _` mp_tac >>
     qpat_x_assum `k + type_memory_size _ <= sz` mp_tac >>
     rpt (pop_assum kall_tac) >>
     pure_rewrite_tac[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `w2n (b + n2w k) = w2n b + k` by simp[arithmeticTheory.ADD_COMM] >>
  `w2n b + sz < dimword (:256)` by decide_tac >>
  `lookup_var x6 u = SOME (b + n2w k + 32w +
      (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv))` by simp[] >>
  drule_all memory_pop_result_address >> strip_tac >>
  `u.vs_memory = (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t).vs_memory` by
    (`1 <= LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[GSYM wordsTheory.n2w_sub]) >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  `tend.scopes = pre ++ env'::rest` by fs[] >>
  `id IN FDOM env'` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  qmatch_asmsub_abbrev_tac `read_result cx result (tend with scopes := scopes')` >>
  `MAP FDOM tend.scopes = MAP FDOM scopes'` by
    (simp[Abbr `scopes'`, finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FLOOKUP_DEF,
      pred_setTheory.ABSORPTION] >>
     qpat_x_assum `id IN FDOM env'` mp_tac >> rpt (pop_assum kall_tac) >> SET_TAC[]) >>
  `lookup_scopes id scopes' = SOME (entry with <|value := updated;
      popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>)` by
    simp[Abbr `scopes'`, lookup_scopes_update] >>
  `!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j tend.scopes` by
    (simp[Abbr `scopes'`] >> metis_tac[lookup_scopes_update_other]) >>
  `k + 32 <= sz` by decide_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  qexistsl_tac [`INL result`, `(tend with gas_obs := []) with scopes := scopes'`,
    `OK (u with vs_inst_idx := LENGTH r.cs_current_insts)`] >>
  conj_tac
  >- (once_rewrite_tac[GSYM APPEND_NIL] >>
      irule gas_marked_exec_bind_normal >> goal_assum drule >>
      simp[Abbr `result`, Abbr `scopes'`]) >>
  disj1_tac >> simp[] >>
  irule (pop_memory_live_suffix_post |> Q.INST [`mid` |-> `tend with gas_obs := []`, `e` |-> `Pop ann bt`]
    |> SRULE [exprSimVVFrameTheory.vv_post_inst_idx, expr_type_def]) >>
  goal_assum (drule_at Any) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_assum `mem_path_offset entry.type path = _` (irule_at Any) >>
  qpat_assum `FLOOKUP cenv.ce_vars id = _` (irule_at Any) >>
  qpat_assum `wb_frame cenv es _ sa s0 t` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
  fs[record_pop_def] >>
  gvs[Abbr `scopes'`] >>
  drule exprSimMemorySourceTheory.read_result_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >>
  full_simp_tac std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

Finalise pop_nested_local_sim

