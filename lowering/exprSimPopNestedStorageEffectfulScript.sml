(*
 * Pop on a nested target: pop_nested_storage_effectful_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedStorageEffectful
Ancestors
  exprSimPopNestedBase exprSimPopNestedStorageFrame
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation
  exprSimHypsDefs targetPlaceLive vyperStorageLayoutSafety
  vyperPlaceStoragePreservation accountsRelProps vyperStorage
  exprSimHash fragGasSeqAbort gasSummary exprSimVVFrame
  gasOutcome gasExemptCert gasSummaryCompose fragGasMode fragGasPath

(* Effectful indices may shrink an ancestor after its pointer is captured.
   Capacity provenance and final-state storage preservation validate the cached
   child region independently of current ancestor lengths. *)
Theorem pop_nested_storage_effectful_dead_case:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) /\
    ~EVERY (storage_frame_expr cx) (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  Cases_on
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `!h w e c i l s. ci_mono s (SND (compile_dynarray_pop h w e c i l s))` by
    simp[ci_mono_compile_dynarray_pop] >>
  `ci_mono sm r` by metis_tac[pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  qpat_x_assum `pop_target_frag _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [pop_target_frag_def]) >>
  disch_then (qspecl_then [`ArrayT ann (Dynamic n)`, `sa`, `sm`,
                           `(hdr,loc,pt)`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_storage_effectful_dead_case[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `tr0`] strip_assume_tac) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `tr0`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  qpat_x_assum `expr_exit (INR exc) tr0` mp_tac >>
  Cases_on `tr0` >> simp[expr_exit_def] >>
  Cases_on `exc` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Resume pop_nested_storage_effectful_dead_case[normal]:
  rename1 `target_post _ _ _ _ _ _ _ _ _ (PlaceR p) _ _ t` >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p, tend with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  drule_all nested_pop_target_storage_preserved >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  drule_all nested_pop_eval_target_storage_class >> strip_tac >> gvs[] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule eval_target_place_region >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME tv` >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all vyperPlaceStoragePreservationTheory.storage_place_region_slots_in_range >>
  strip_tac >>
  drule_all accountsRelPropsTheory.storage_place_region_read_live >> strip_tac >>
  drule_all pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def] >>
  `ws = 1` by
    (Cases_on `tr` >> fs[Abbr `ws`, Abbr `lc`, slot_loc_def, word_scale_def]) >>
  qunabbrev_tac `lc` >> qunabbrev_tac `ws` >>
  gvs[Abbr `esz`] >>
  simp[slot_loc_def] >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME tv` >>
  Cases_on `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
              (tend with gas_obs := [])` >>
  rename1 `_ = (pres, pend)` >>
  mp_tac (Q.INST [`es` |-> `tend with gas_obs := []`, `es0` |-> `es`,
                  `res` |-> `pres`, `es'` |-> `pend`,
                  `pt` |-> `SOME (ValPT (ArrayT ann (Dynamic n)))`]
          nested_pop_storage_live_suffix_sim) >>
  impl_tac >- fs[slot_loc_def] >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`pres'`, `pend'`, `pr`]
                (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`pres'`, `pend'`, `pr`] >>
  conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
             |> REWRITE_RULE [APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
        (irule_at Any) >>
      asm_rewrite_tac[]) >>
  gvs[]
QED

Finalise pop_nested_storage_effectful_dead_case

Theorem pop_nested_storage_effectful_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  Cases_on `EVERY (storage_frame_expr cx) (target_indices bt)`
  >- (irule pop_nested_storage_frame_sim >> metis_tac[]) >>
  irule pop_nested_storage_effectful_dead_case >> metis_tac[]
QED
