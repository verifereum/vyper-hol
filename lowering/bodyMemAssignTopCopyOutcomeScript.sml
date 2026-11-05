(* Full counted statement outcome for a static aggregate storage copy. *)
Theory bodyMemAssignTopCopyOutcome
Ancestors
  bodyMemAssignTopCopySuffix bodyMemAssignTopCopySem bodyMemAssignTopCopyFacts
  bodyMemAssignTopWord bodyMemoryDefs bodyMemoryPreds
  exprSimMemDefs exprSimDefs exprSimSource exprSimProps exprLoweringProps
  stmtSimDefs stmtSimProps stmtSimAssignStorage stmtSimAssignStorageCopy stmtSimForced
  stmtLowering stmtLoweringMono exprSimTopLevelProps fragExec exprLowering emitHelper emitHelperProps compileEnv context
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
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by simp[] >>
  drule_all topcopy_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op, sB)` >> gvs[] >>
  drule (INST_TYPE [alpha |-> ``:num # num``] topcopy_no_dyn_info) >>
  disch_then (qspec_then
    `\elem. ((type_memory_bytes cenv elem + 31) DIV 32,
             type_memory_bytes cenv elem)` assume_tac) >> fs[] >>
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
    (irule topcopy_suffix_open >> goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     `ci_mono sB sb` by
       metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
     fs[ci_mono_def] >> decide_tac) >>
  irule forced_then_outcome >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `\v ee t.
    expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sB.cs_current_bb /\
    t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac >- suspend "success" >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >> simp[]
QED

Resume compile_assign_storage_copy_stmt_frag_mem[success]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `value_has_type tvt v` by metis_tac[] >>
  `~cx.txn.is_static` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule_all topcopy_typed_storage_write >>
  disch_then (qspecl_then [`tr`, `n2w slot`, `ee`] mp_tac) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `write_storage_slot cx tr (n2w slot) tvt v ee = (INL (), ee')` >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  drule_all (SRULE [] storage_copy_success_run_mem) >> strip_tac >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  `ee'.gas_obs = [] /\ ee'.scopes = ee.scopes` by
    (Cases_on `tr` >> simp[Abbr `ee'`, set_storage_def]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `ee'`, `OK u`] >>
  conj_tac >- metis_tac[topcopy_write_storage_gas_tail] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> metis_tac[]
QED

Finalise compile_assign_storage_copy_stmt_frag_mem
