(* Full counted statement outcome for a static aggregate storage copy. *)
Theory bodyMemAssignTopCopyOutcome
Ancestors
  bodyMemAssignTopCopySuffix bodyMemAssignTopCopySem bodyMemAssignTopCopyFacts
  bodyMemAssignTopWord bodyMemoryDefs bodyMemoryPreds
  exprSimMemDefs exprSimDefs exprSimSource exprSimProps exprLoweringProps
  stmtSimDefs stmtSimProps stmtSimAssignStorage stmtSimAssignStorageCopy stmtSimForced
  stmtLowering stmtLoweringMono exprSimTopLevelProps fragExec exprLowering emitHelper emitHelperProps compileEnv loweringStateRelDefs context
  gasOutcome gasSummary fragGasMode fragGasPath gasContext
  vyperStorageLayoutSafety vyperStorageBackend vyperStorage vyperValue
  loweringPosts bodySim vyperState list rich_list finite_map words arithmetic
Libs
  monadsyntax

Theorem compile_assign_storage_copy_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ ~has_length_word typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    ~is_abi_dynamic cenv.ce_struct_fields typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (n2w slot, tvt) ==>
       ranges_disjoint slot (type_slot_size tvt) (w2n k') (type_slot_size tv')) /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==> value_has_type tvt v) /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type e = typ` (SUBST_ALL_TAC o SYM) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by simp[] >>
  drule_all assign_storage_copy_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op, sB)` >> gvs[] >>
  fs[] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th])) >>
  drule forced_then_admissible >> strip_tac >>
  `~block_is_terminated sb` by
    (irule assign_storage_copy_suffix_open >> goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     `ci_mono sB sb` by
       metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
     fs[ci_mono_def] >> decide_tac) >>
  irule forced_then_outcome >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es sa sB s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sB.cs_current_bb /\
    t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
      simp[vyperStorageTraceTheory.storage_trace_frame_event,
           vyperStorageTraceTheory.storage_trace_frame_write_storage_slot])
  >~ [`expr_exit (INR _) _`]
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >~ [`gas_outcome _ _ _ _ _ (bind (eval_expr _ _) _) _ _ _`]
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `sB`, `op`, `s0`] mp_tac) >> simp[]) >>
  suspend "success"
QED

Resume compile_assign_storage_copy_stmt_frag_mem[success]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `valid_horizon cx st0 H1 ee.storage_trace` >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gs).storage_trace`
       suffices_by simp[] >>
     metis_tac[vyperStorageFootprintTheory.valid_horizon_frame]) >>
  `expr_post H1 ctx func cenv cx e es sa sB s0 ee v op t /\
   expr_store_bound cx (expr_type e) v op t /\
   t.vs_current_bb = sB.cs_current_bb /\
   t.vs_inst_idx = LENGTH sB.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[] >>
  `value_has_type tvt v` by
    (qpat_x_assum `!gs v es1. _ ==> value_has_type _ _` irule >>
     fs[ETA_THM] >> metis_tac[]) >>
  `~cx.txn.is_static` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule typed_storage_copy_write >>
  disch_then (qspecl_then [`cx`, `tr`, `n2w slot`, `ee`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all (SRULE [] storage_copy_success_run_mem) >> strip_tac >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  qabbrev_tac `ee' = set_storage cx ee tr
    (apply_writes (n2w slot) writes (get_storage cx ee tr))` >>
  `ee'.gas_obs = [] /\ ee'.scopes = ee.scopes` by
    (Cases_on `tr` >> simp[Abbr `ee'`, set_storage_def]) >>
  qabbrev_tac `ef = ee' with storage_trace :=
    ee.storage_trace ++ [StorageRoot tr slot tvt]` >>
  `ef with gas_obs := [] = ef` by
    simp[Abbr `ef`, evaluation_state_component_equality] >>
  `!tail. ignore_bind (record_storage_event (StorageRoot tr slot tvt))
            (write_storage_slot cx tr (n2w slot) tvt v) (ee with gas_obs := tail) =
          (INL (), ef with gas_obs := tail)` by
    (gen_tac >>
     simp[ignore_bind_def, bind_def, record_storage_event_def, return_def] >>
     `write_storage_slot cx tr (n2w slot) tvt v (ee with gas_obs := tail) =
        (INL (), ee' with gas_obs := tail)` by
       fs[write_storage_slot_gas_obs] >>
     drule write_storage_slot_storage_trace >>
     disch_then (qspec_then `ee.storage_trace ++ [StorageRoot tr slot tvt]`
       mp_tac) >>
     simp[Abbr `ef`]) >>
  qexistsl_tac [`INL ()`, `ef`, `OK u`] >>
  rpt conj_tac
  >- (BETA_TAC >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC >>
  disj1_tac >> simp[] >> qx_gen_tac `H` >> strip_tac >>
  `ef.storage_trace = ee.storage_trace ++ [StorageRoot tr slot tvt]` by
    simp[Abbr `ef`] >>
  `valid_horizon cx st0 H ee.storage_trace /\
   MEM (tr, n2w slot, tvt) (FST H) /\ regions_consistent (FST H) /\
   storage_locks_separated (FST H) (SND H)` by
    (qpat_x_assum `valid_horizon _ _ H ef.storage_trace` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
          vyperStorageFootprintTheory.storage_observations_ok_def,
          vyperStorageFootprintTheory.storage_trace_regions_def,
          listTheory.EVERY_APPEND]) >>
  `expr_post H ctx func cenv cx e es sa sB s0 ee v op t` by metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx ee' u` by
    (qpat_x_assum `!H. expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ ==> _`
       irule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ef u` by simp[Abbr `ef`] >>
  `storage_well_formed_on cx ee (FST H)` by fs[expr_post_def] >>
  `storage_well_formed_on cx ef (FST H)` by
    (`well_formed_type_value tvt` by
       metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     `storage_well_formed_on cx ee' (FST H)` by
       metis_tac[vyperStorageFootprintTheory.typed_write_preserves_storage_well_formed_on] >>
     pop_assum mp_tac >>
     simp[Abbr `ef`, vyperStorageFootprintTheory.storage_well_formed_on_def,
          get_storage_def]) >>
  `ef.scopes = ee.scopes` by simp[Abbr `ef`] >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> metis_tac[]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]
QED

Finalise compile_assign_storage_copy_stmt_frag_mem
