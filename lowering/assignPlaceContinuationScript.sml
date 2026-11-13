Theory assignPlaceContinuation
Ancestors
  loweringStateRelDefs
  assignPlaceCallerFacts assignPlaceStoreReady assignPlaceGasCompose assignPlaceEndpoint
  assignPlaceOperandFacts targetWalkVvFrame targetPlaceSimCases
  stmtSimAugAssignPlaceMemory assignPlaceTargetLive exprSimHyps
  exprOperandVar exprSimAggregateSource exprSimSource
  stmtLoweringMono stmtSimDeclCompose targetPlaceSimDefs targetPlaceSim loweringPosts
  compileEnv stmtSimDefs vyperExprNoControl
  exprSimHypsDefs exprLowering vyperStoragePlaceProvenance bodySimAugPlaceLoad
  supportedExprTraverse vyperTypeCallGraph
Libs monadsyntax

(* Collect the static supported-callee facts from each target index. *)
Theorem target_indices_pre_static[local]:
  !bt. target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (\c. FST c = NONE /\
             ?tops. supported_program tops /\
                    get_module_code cx NONE = SOME tops /\
                    IS_SOME (supported_function_decl tops c Internal))
    (int_calls_target bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_pre_def, supported_expr_exists_def,
       int_calls_expr_def] >>
  strip_tac >> rename1 `target_indices_pre cenv cx env tgt` >>
  first_x_assum (qspec_then `tgt` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >> strip_tac >> fs[] >>
  res_tac >> fs[expr_body_pre_def, expr_has_evm_run_def]
QED

Theorem assign_place_pure_continuation:
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
     function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  EVERY (\c. FST c = NONE) (int_calls_target bt) /\
  type_place_target env bt = SOME (Type dty) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  assignable_type env.type_defs (expr_type e) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
  assign_alloc_ok cenv bt e /\ target_indices_pre cenv cx env bt /\
  expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ ~expr_has_effect e /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (tr,st) /\
  unwrap_value cenv vv st = (src,su) /\
  (case FST (SND tr) of
     SOME loc => compile_assign_value cenv (FST tr) loc src
       (is_word_type (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e))
       (vv_location vv)
       (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e)
       (lowered_value_type cenv e)
       (case (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e) of
          ArrayT et (Dynamic _) =>
            SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
        | _ => NONE)
       (type_memory_bytes cenv (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e))
   | NONE => emit_void INVALID []) su = ((),sb) /\
  ci_mono sa sm /\ ci_mono sm st /\ ci_mono st su /\ ci_mono su sb /\
  fn_has_code sa sm func /\ fn_has_code sm st func /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL pv) mid (OK t) /\
  vv_post ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) pv vv t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (read_result cx pv)
      (\v. bind (eval_target_place cx bt) (\p. write_place cx p v)))
    (mid with gas_obs := [],t)
    (\res ee u. !tail. stmt_post ctx func cx lctx cenv cenv sa sb es s0
      res (ee with gas_obs := tail) u)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v. read_result cx pv (mid with gas_obs := []) =
       (INL v,mid with gas_obs := [])` by
    metis_tac[vv_post_materialises] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (drule stmtSimAugAssignTheory.gas_marked_exec_observation >>
     disch_then (qspec_then `[]` assume_tac) >>
     metis_tac[expr_body_pre_eval_result, expr_body_pre_gas_obs]) >>
  `target_sim ctx func cenv cx env bt (mid with gas_obs := [])` by
    metis_tac[target_case_def, target_pre_def] >>
  `vv_storage_live cx vv (mid with gas_obs := []) t` by
    gvs[vv_post_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!l. vv_operand vv <> Label l` by
    metis_tac[assign_place_operand_not_label] >>
  `~t.vs_halted` by
    (irule aug_place_marked_path_not_halted >>
     fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!tail. read_result cx pv (mid with gas_obs := tail) =
      (INL v,mid with gas_obs := tail)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok
      (mid with gas_obs := [])` by
    (rewrite_tac[gasContextTheory.gas_admissible_def] >>
     rpt gen_tac >> disch_tac >>
     Cases_on `res` >- simp[target_place_res_ok_def] >>
     rename1 `INR ex` >>
     `no_control_exc ex` by metis_tac[vyperExprNoControlTheory.eval_target_place_no_control] >>
     `stmt_res_ok lctx (INR ex)` by
       (drule gasContextTheory.gas_admissible_result >> disch_then irule >>
        drule stmtSimAugAssignTheory.gas_marked_exec_observation >>
        disch_then (qspec_then `gs` assume_tac) >>
        qexistsl_tac [`ee`, `gas_explicit marks s0.vs_gas_readings ++ gs`] >>
        gnvs[] >>
        simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]) >>
     gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok
      (mid with gas_obs := [])` by
    (rewrite_tac[gasContextTheory.gas_admissible_def] >>
     rpt gen_tac >> disch_tac >>
     Cases_on `res` >- simp[target_res_ok_def] >>
     rename1 `INR ex` >>
     `target_place_res_ok (INR ex)` by
       (drule gasContextTheory.gas_admissible_result >> disch_then irule >>
        qexistsl_tac [`ee`, `gs`] >> gnvs[] >>
        simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]) >>
     gvs[target_res_ok_def, target_place_res_ok_def]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `vv_post ctx func cenv cx e es sa sm s0 (mid with gas_obs := [])
      (Value v) vv t` by metis_tac[exprSimUnwrapPropsTheory.vv_post_read_result] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ pv _ _` kall_tac >>
  `EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
      IS_SOME (supported_function_decl (cx_tops cx) c Internal))
      (int_calls_target bt)` by
    (drule_all target_indices_pre_static >>
     simp[listTheory.EVERY_MEM] >> metis_tac[optionTheory.SOME_11]) >>
  drule_all target_walk_vv_frame >>
  disch_then assume_tac >>
  `gas_marked_exec F (ctx,func) (read_result cx pv)
      (mid with gas_obs := [],t) [] (INL v) mid (OK t)` by
    (simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_rules]) >>
  irule exprSimExtract32CountedTheory.extract32_outcome_read_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_assoc] >>
  irule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (BETA_TAC >> Cases >- simp[exprSimDefsTheory.expr_exit_INL] >>
      rpt gen_tac >> strip_tac >> qexists_tac `y` >>
      simp[stmt_exit_def] >> rpt gen_tac >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  reverse conj_tac >- (rpt gen_tac >> BETA_TAC >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `?p. v' = PlaceR p` by
    (qpat_x_assum `INL _ = INL _` (assume_tac o SRULE []) >>
     fs[target_post_def] >> Cases_on `pv'` >> gvs[place_ptr_rel_def]) >>
  gnvs[] >>
  simp[vyperStateTheory.get_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def] >>
  `local_ptrs_reserved cenv st /\ sa.cs_next_id <= st.cs_next_id /\
   (!x. vv_operand vv = Var x ==> not_fresh_at st x)` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `sm` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
     conj_tac
     >- (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `~t'.vs_halted` by
    (irule aug_place_marked_path_not_halted >>
     fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `read_result cx (Value v) (mid' with gas_obs := []) =
      (INL v,mid' with gas_obs := [])` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `eval_base_place cx bt
      (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
      (INL (PlaceR p),mid' with gas_obs := [])` by
    (drule stmtSimAugAssignTheory.gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `eval_target_place cx bt
      (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
      (INL p,mid' with gas_obs := [])` by
    simp[Once vyperInterpreterTheory.evaluate_def,
         vyperStateTheory.bind_def, vyperStateTheory.get_place_def,
         vyperStateTheory.return_def] >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := [])` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     qexistsl_tac [`INL p`, `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`, `bt`] >>
     simp[]) >>
  `expr_body_pre cenv cx env e (mid' with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  drule_all exprSimAggregateBodyCountedTheory.unwrap_value_body_rebased_path >>
  strip_tac >>
  `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
  `?dst loc. tr = (dst,SOME loc,SOME (ValPT dty)) /\
       loc <> LocCode /\ loc <> LocCalldata` by
    (fs[target_post_def] >> Cases_on `p` >>
     gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[] >>
     PairCases_on `tr` >> gvs[value_type_place_def]) >>
  gnvs[] >>
  `eval_expr cx e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
          gas_explicit marks' t.vs_gas_readings) =
      (INL pv,mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`
       (mp_tac o Q.GEN `tail` o MATCH_MP stmtSimAugAssignTheory.gas_marked_exec_observation) >>
     disch_then (qspec_then `gas_explicit marks' t.vs_gas_readings` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
          gas_explicit marks' t.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt v` by metis_tac[] >>
  `!res ff. write_place cx p v (mid' with gas_obs := []) = (res,ff) ==>
      stmt_res_ok lctx res` by
    (rpt strip_tac >>
     qpat_x_assum `gas_admissible (eval_target_place _ _) _ _` kall_tac >>
     qpat_x_assum `gas_admissible (eval_base_place _ _) _ _` kall_tac >>
     drule gasContextTheory.gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ff`, `gas_explicit marks s0.vs_gas_readings ++
         gas_explicit marks' t.vs_gas_readings`] >>
     simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?dw dtv. eval_operand dst t' = SOME dw /\
       place_ptr_rel cenv cx t' (PlaceR p) dw (SOME loc) (Type dty) /\
       evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[target_post_def] >> metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type]) >>
  `~cx.txn.is_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  Cases_on `write_place cx p v (mid' with gas_obs := [])` >>
  rename1 `write_place cx p v (mid' with gas_obs := []) = (wr,ff)` >>
  `stmt_res_ok lctx wr` by metis_tac[] >>
  `wr = INL ()` by
    (Cases_on `p`
     >- gvs[vyperPlaceFramesTheory.write_storage_place_eq, AllCaseEqs(), stmt_res_ok_def]
     >- metis_tac[assign_place_pure_memory_write_success] >>
     fs[place_ptr_rel_def]) >>
  gnvs[] >>
  `(!x. src = Var x ==> not_fresh_at su x) /\
   (!x. dst = Var x ==> not_fresh_at su x)` by
    (conj_tac
     >- (`(case vv of
             StackValue ty op => (!x. op = Var x ==> not_fresh_at st x)
           | LocatedValue ty pp => (!x. pp.ptr_operand = Var x ==> not_fresh_at st x))` by
           (Cases_on `vv` >> fs[contextTheory.vv_operand_def]) >>
         metis_tac[compiler_unwrap_value_var]) >>
     fs[target_post_def, exprLoweringPropsTheory.ci_mono_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `!x. dst = Var x ==> not_fresh_at st x` by
    fs[target_post_def] >>
  `!l. dst <> Label l` by
    (drule_all targetSubscriptSplitTheory.target_subscript_typed_base_not_label >> simp[]) >>
  `eval_operand dst u = SOME dw` by
    (Cases_on `dst` >>
     gnvs[venomStateTheory.eval_operand_def, expr_post_def] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ /\ _` strip_assume_tac >>
     first_x_assum irule >> fs[not_fresh_at_def]) >>
  `place_ptr_rel cenv cx u (PlaceR p) dw (SOME loc) (Type dty)` by
    (Cases_on `p` >> gvs[place_ptr_rel_def] >>
     fs[expr_post_def, local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv su` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `st` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `post_value_type cenv e = expr_type e /\
   assignable_type (get_tenv cx) dty /\
   0 < type_slot_size dtv /\ 0 < type_memory_size dtv` by
    (irule assign_place_caller_store_types >>
     metis_tac[]) >>
  `!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id mid'.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    metis_tac[aug_place_store_entry_types] >>
  `(loc <> LocMemory /\ ~is_word_type dty /\ dty <> lowered_value_type cenv e /\
    ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
    type_alloc_ok cenv dty)` by
    (strip_tac >>
     `loc = LocStorage \/ loc = LocTransient` by
       (qpat_x_assum `place_ptr_rel cenv cx u _ _ _ _` mp_tac >>
        qpat_x_assum `loc <> LocMemory` mp_tac >>
        Cases_on `p` >> simp[place_ptr_rel_def, slot_loc_def] >>
        rpt strip_tac >> gnvs[] >> simp[] >> metis_tac[]) >>
     drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)
       assign_place_caller_normalization_alloc >>
     disch_then (qspec_then `e` mp_tac) >> simp[] >> metis_tac[]) >>
  `?z. gas_marked_path F ctx func u 0 (OK z) /\
       stmt_state_rel ctx func cenv cx ff z /\
       (!x. not_fresh_at su x ==> lookup_var x z = lookup_var x u) /\
       (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==>
                FLOOKUP z.vs_allocas aid = SOME b) /\
       ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_frame cenv (mid' with gas_obs := []) su u cenv ff z` by
    (irule assign_place_store_from_expr_post >> simp[] >>
     (conj_tac >- metis_tac[expr_sim_inv_gas_obs]) >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >> simp[] >>
     qexistsl_tac [`env`, `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
        gas_explicit marks' t.vs_gas_readings`] >>
     simp[vyperStateTheory.bind_def]) >>
  `gas_marked_path F ctx func t' 0 (OK z)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `!tail. write_place cx p v (mid' with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    (qpat_x_assum `write_place _ _ _ _ = (INL (),ff)` mp_tac >>
     Cases_on `p`
     >- (pure_rewrite_tac[vyperStateTheory.write_place_def] >>
         rpt strip_tac >>
         qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
         simp[stmtSimAssignStorageTheory.write_storage_slot_gas_obs] >>
         strip_tac >>
         qpat_x_assum `_ with gas_obs := [] = ff` (SUBST1_TAC o SYM) >> simp[])
     >- (strip_tac >> drule aug_place_memory_write_gas_obs >>
         simp[] ) >>
     fs[place_ptr_rel_def]) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK z`] >>
  (conj_tac >- simp[gasSummaryTheory.gas_marked_exec_def,
                         vyperStateTheory.bind_def, vyperStateTheory.return_def]) >>
  disj1_tac >> qexists_tac `z` >> simp[] >>
  gen_tac >> rewrite_tac[stmt_post_end_gas_obs] >>
  rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl] >>
  reverse conj_tac
  >- (`MAP FDOM mid'.scopes = MAP FDOM es.scopes` by
        (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
         drule vyperEvalExprPreservesScopesDomTheory.eval_base_place_preserves_scopes_dom >>
         simp[] >> metis_tac[]) >>
      `alloca_frame cenv es sa s0 cenv mid' t'` by
        (qpat_assum `wb_frame _ es _ sa s0 t'`
           (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
         irule alloca_frame_of_mem_frame >>
         qpat_assum `stmt_state_rel _ _ _ _ es s0` (irule_at Any) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `alloca_frame cenv mid' (sa with cs_next_var := st.cs_next_var) t' cenv mid' u` by
        (`local_ptrs_reserved cenv (sa with cs_next_var := st.cs_next_var)` by
           (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
            qexists_tac `st` >> simp[]) >>
         `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
           fs[vv_post_def] >>
         drule_at (Pat `expr_post _ _ _ _ _ _ _ _ t' _ _ _ u`) expr_post_alloca_frame >>
         simp[alloca_frame_def, local_region_def]) >>
      qpat_x_assum `wb_frame _ es _ sa s0 t'` mp_tac >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ t' _ _ _ u` mp_tac >>
      pure_rewrite_tac[expr_post_def, wb_frame_def] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[] >>
      `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id` by
        fs[exprLoweringPropsTheory.ci_mono_def] >>
      (conj_tac >-
        (rpt strip_tac >>
         `lookup_var x t' = SOME w` by
           (first_x_assum irule >> simp[]) >>
         `lookup_var x u = SOME w` by
           (qpat_x_assum `!x w. not_fresh_at (sa with cs_next_var := _) x /\ _ ==> _`
              (qspecl_then [`x`, `w`] mp_tac) >>
            simp[] >> disch_then irule >>
            irule freshWritesTheory.not_fresh_at_mono >>
            qexists_tac `sa` >> simp[] >>
            fs[exprLoweringPropsTheory.ci_mono_def]) >>
         qpat_x_assum `!x. not_fresh_at su x ==> _` (qspec_then `x` mp_tac) >>
         impl_tac >- (irule freshWritesTheory.not_fresh_at_mono >>
           qexists_tac `sa` >> simp[]) >>
         simp[])) >>
      `alloca_frame cenv es sa s0 cenv mid' u` by
        (irule alloca_frame_trans >>
         qexistsl_tac [`cenv`, `mid'`, `t'`, `sa with cs_next_var := st.cs_next_var`] >>
         simp[]) >>
      irule alloca_frame_trans >>
      qexistsl_tac [`cenv`, `mid'`, `u`, `su`] >>
      simp[] >> metis_tac[]) >>
  `gas_marked_path F ctx func s0 (LENGTH marks) (OK t)` by
    fs[gasSummaryTheory.gas_marked_exec_def] >>
  `gas_marked_path F ctx func t (LENGTH marks') (OK t')` by
    fs[gasSummaryTheory.gas_marked_exec_def] >>
  `~block_is_terminated sm` by
    metis_tac[endpoint_path_open, exprLoweringPropsTheory.ci_mono_def] >>
  `~block_is_terminated st` by
    metis_tac[endpoint_path_open, exprLoweringPropsTheory.ci_mono_def] >>
  `~block_is_terminated su` by
    metis_tac[endpoint_path_open, exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[endpoint_path_open, exprLoweringPropsTheory.ci_mono_def]
QED
