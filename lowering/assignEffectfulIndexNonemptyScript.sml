Theory assignEffectfulIndexNonempty
Ancestors
  assignEffectfulIndexCode assignEffectfulIndexSnapshotRun
  assignPlaceGasCompose assignPlaceCallerFacts assignPlaceEndpoint
  stmtSimDeclCompose stmtLoweringMono targetPlaceSimCases bodySim
  exprSimHyps exprSimAggregateSource exprOperandVar
  stmtSimDefs exprLoweringProps compileEnv loweringPosts exprSimDefs stmtSimAssignMem
  exprSimProps stmtSimAugAssign stmtSimAugAssignPlaceMemory
  vyperEvalExprPreservesScopesDom exprSimHypsDefs exprSimSource
  targetPlaceSim vyperExprNoControl bodySimAugPlaceLoad
  immutableDeployPhysicalSource assignEffectfulIndexSnapshotFrame
  vyperStoragePlaceProvenance exprLowering
  vyperTypeEvalSoundness vyperTypeCallStackSoundness tuplePlaceWriteOutcome
  tuplePlaceBounds aggregateEvaluatedLayout valueEncodingProps context
  abiStepAllocRecords venomExecProofs placeRelayoutFrag

Theorem snapshot_gas_edge_allocations[local]:
  gas_path_edge ctx func s n (OK t) ==> s.vs_allocas SUBMAP t.vs_allocas
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def] >>
  imp_res_tac step_inst_allocas_extend >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  gvs[venomStateTheory.jump_to_def] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem snapshot_gas_allocations[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> s.vs_allocas SUBMAP t.vs_allocas
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >> rpt strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  metis_tac[snapshot_gas_edge_allocations, finite_mapTheory.SUBMAP_TRANS]
QED

Theorem snapshot_marked_lookup[local]:
  gas_marked_path memory ctx func s n (OK t) /\
  FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b
Proof
  metis_tac[fragGasModeTheory.gas_marked_path_exec,
            snapshot_gas_allocations, finite_mapTheory.SUBMAP_FLOOKUP_EQN]
QED

Theorem effectful_target_live[local]:
  type_place_target env bt = SOME (Type ty) /\
  expr_sim_inv cenv cx env st /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,st') ==>
  live_memory_result st' (PlaceR p)
Proof
  strip_tac >>
  mp_tac (cj 3 (SPEC_ALL (cj 8 eval_scc_type_sound_results_mutual))) >>
  disch_then (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
  fs[expr_sim_inv_def, vyperTypeSystemTheory.well_typed_target_def] >>
  metis_tac[]
QED

Theorem assign_place_mutating_nonempty_case_with_store:
  (!ee ss st u mid p dty dst loc s stv dtv v snap sw sf dw ff.
    target_post ctx func cenv cx ee ss st u mid (PlaceR p) (Type dty)
      (dst,SOME loc,SOME (ValPT dty)) s /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ val_wf stv v /\
    eval_operand (vv_operand snap) u = SOME sw /\
    (!x. vv_operand snap = Var x ==> not_fresh_at ss x) /\
    (!l. vv_operand snap <> Label l) /\
    ss.cs_next_var <= st.cs_next_var /\ ss.cs_next_id <= st.cs_next_id /\
    (if is_word_type (lowered_value_type cenv e) then
       vv_location snap = NONE /\ sw = typed_val_to_w256 stv v
     else vv_location snap = SOME LocMemory /\
       val_in_memory stv v (w2n sw) u.vs_memory /\
       ?aid sz. aid < ss.cs_next_id /\
         FLOOKUP u.vs_allocas aid = SOME (w2n sw,sz) /\
         type_memory_size stv <= sz /\
         (!n b len. local_region cenv ee.scopes u n b len ==>
           w2n sw + sz <= b \/ b+len <= w2n sw)) /\
    compile_assign_value cenv dst loc (vv_operand snap) (is_word_type dty)
      (vv_location snap) dty (lowered_value_type cenv e)
      (case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et + 31) DIV 32,
               type_memory_bytes cenv et) | _ => NONE)
      (type_memory_bytes cenv dty) st = ((),sf) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    expr_sim_inv cenv cx env mid /\ cenv.ce_target CapMcopy /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv st /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (loc = LocMemory ==> w2n dw + type_memory_size dtv < dimword (:256)) /\
    (loc = LocMemory ==> 0 < type_memory_size dtv) /\
    (loc = LocMemory /\ (is_word_type (lowered_value_type cenv e) \/
      dty = lowered_value_type cenv e) ==>
      type_memory_size dtv + 64 < dimword (:256)) /\
    (loc = LocMemory /\ ~is_word_type (lowered_value_type cenv e) ==>
      0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256)) /\
    eval_operand dst s = SOME dw /\ 0 < type_slot_size dtv /\
    (loc <> LocMemory /\ dty <> lowered_value_type cenv e /\
      ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
      type_alloc_ok cenv dty) /\
    write_place cx p v mid = (INL (),ff) /\
    fn_has_code st sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?z. gas_marked_path F ctx func s 0 (OK z) /\
      stmt_state_rel ctx func cenv cx ff z /\
      (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
      ~z.vs_halted /\ z.vs_current_bb = sf.cs_current_bb /\
      z.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_frame cenv mid st s cenv ff z) /\
  expr_can_mutate cenv (target_to_expr bt) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  ~supported_target_pure tops bt /\
  type_place_target env bt = SOME (Type dty) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  assignable_type env.type_defs (expr_type e) /\
  ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                         read_result cx pv sread = (INL v,s2)) ==>
   target_case F ctx func cenv cx bt) /\
  ~immutable_root cx bt /\ assign_alloc_ok cenv bt e /\
  target_indices_pre cenv cx env bt /\
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  body_inv tops ctx cenv cx /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
    (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule assign_effectful_value_code >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  `ci_mono sa sr` by
    metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sr ss` by
    metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  `ci_mono ss st` by
    metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono st su` by
    metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su sb` by
    (qpat_x_assum `case FST (SND r) of NONE => _ | SOME loc => _` mp_tac >>
     Cases_on `FST (SND r)` >> simp[] >> strip_tac >>
     metis_tac[ci_mono_stmt_helpers, ci_mono_emit_void, pairTheory.SND]) >>
  `fn_has_code sa sr func /\ fn_has_code sr ss func /\
   fn_has_code ss st func /\ fn_has_code st su func /\
   fn_has_code su sb func` by
    metis_tac[ci_mono_def, fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  irule assign_place_result_outcome >>
  qexistsl_tac [
    `\res ee r. expr_exit res r`,
    `\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sr s0 ee tv vv0 t /\
       t.vs_current_bb = sr.cs_current_bb /\
       t.vs_inst_idx = LENGTH sr.cs_current_insts`] >>
  conj_tac
  >- (BETA_TAC >> Cases >- simp[exprSimDefsTheory.expr_exit_INL] >>
      rpt gen_tac >> strip_tac >> qexists_tac `y` >>
      simp[stmt_exit_def] >> rpt gen_tac >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      qpat_x_assum `INL _ = INL _` (assume_tac o SRULE []) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      suspend "continuation") >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then irule >> simp[] >>
  metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible]
QED

Resume assign_place_mutating_nonempty_case_with_store[continuation]:
  `?v. read_result cx pv (mid with gas_obs := []) =
       (INL v,mid with gas_obs := [])` by metis_tac[vv_post_materialises] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL pv,mid with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `vv_post ctx func cenv cx e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
       sa sr s0 (mid with gas_obs := []) pv vv0 t` by simp[vv_post_initial_gas] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at sr x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `~t.vs_halted` by
    (irule aug_place_marked_path_not_halted >>
     fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `?u tv w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    gas_marked_path F ctx func t 0 (OK u) /\
    stmt_state_rel ctx func cenv cx (mid with gas_obs := []) u /\
    eval_operand (vv_operand vv) u = SOME w /\
    (!x. vv_operand vv = Var x ==> not_fresh_at ss x) /\
    (!lbl. vv_operand vv <> Label lbl) /\
    (if is_word_type (lowered_value_type cenv e) then
       vv_location vv = NONE /\ w = typed_val_to_w256 tv v
     else vv_location vv = SOME LocMemory /\
       val_in_memory tv v (w2n w) u.vs_memory /\
       ?aid. sr.cs_next_id <= aid /\ aid < ss.cs_next_id /\
         FLOOKUP u.vs_allocas aid =
           SOME (w2n w,type_memory_bytes cenv (lowered_value_type cenv e)) /\
         (!n b sz. local_region cenv (mid with gas_obs := []).scopes u n b sz ==>
           w2n w + type_memory_bytes cenv (lowered_value_type cenv e) <= b \/
           b+sz <= w2n w)) /\
    (!x. not_fresh_at sr x ==> lookup_var x u = lookup_var x t) /\
    alloca_frame cenv (mid with gas_obs := []) sr t cenv (mid with gas_obs := []) u /\
    ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\
    u.vs_inst_idx = LENGTH ss.cs_current_insts` by
    (irule assign_effectful_snapshot_path >>
     qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_expr _ _ _ = _` (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ _ (_ with gas_obs := _) _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `env` >> simp[] >> fs[ci_mono_def]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval_result] >>
  `target_sim ctx func cenv cx env bt (mid with gas_obs := [])` by
    metis_tac[target_case_def, target_pre_def] >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> fs[ci_mono_def]) >>
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
        drule gas_marked_exec_observation >>
        disch_then (qspec_then `gs` assume_tac) >>
        qexistsl_tac [`ee`, `gas_explicit marks s0.vs_gas_readings ++ gs`] >>
        gnvs[] >>
        simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]) >>
     qpat_x_assum `stmt_res_ok _ _` mp_tac >>
     qpat_x_assum `no_control_exc _` mp_tac >>
     simp[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def] >>
     Cases_on `ex` >> simp[]) >>
  irule gas_outcome_zero_prefix >>
  qpat_assum `gas_marked_path _ _ _ t _ _` (irule_at Any) >>
  `gas_marked_exec F (ctx,func) (read_result cx pv)
      (mid with gas_obs := [],u) [] (INL v) mid (OK u)` by
    (simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_rules]) >>
  irule exprSimExtract32CountedTheory.extract32_outcome_read_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  irule assign_place_target_outcome >>
  drule_all target_place_sim >> disch_then (irule_at Any) >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      qexists_tac `p` >> simp[] >> suspend "store") >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  Cases_on `res` >- gvs[exprSimDefsTheory.expr_exit_INL] >>
  qexists_tac `y` >> simp[stmt_exit_def] >> rpt gen_tac >> disj1_tac >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume assign_place_mutating_nonempty_case_with_store[store]:
  `eval_target_place cx bt
      (mid with gas_obs := gas_explicit marks' u.vs_gas_readings) =
      (INL p,mid' with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := [])` by
    (irule aug_place_target_inv >> goal_assum (drule_at Any) >>
     metis_tac[expr_sim_inv_gas_obs]) >>
  `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
  `?dst loc. r = (dst,SOME loc,SOME (ValPT dty)) /\
      loc <> LocCode /\ loc <> LocCalldata` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[target_post_def] >> strip_tac >> Cases_on `p` >>
     gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[] >>
     PairCases_on `r` >> gvs[value_type_place_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    metis_tac[immutable_rhs_physical_widens] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeCallGraphTheory.int_calls_stmt_def,
          vyperTypeCallGraphTheory.int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  `live_memory_result (mid' with gas_obs := []) (PlaceR p)` by
    (irule effectful_target_live >> goal_assum (drule_at Any) >>
     metis_tac[expr_sim_inv_gas_obs]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type] >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[target_post_def]) >>
  `expr_sim_inv cenv cx env
      (mid with gas_obs := gas_explicit marks' u.vs_gas_readings)` by
    metis_tac[expr_sim_inv_gas_obs] >>
  `?ff. write_place cx p v (mid' with gas_obs := []) = (INL (),ff)` by
    (Cases_on `write_place cx p v (mid' with gas_obs := [])` >>
     rename1 `write_place _ _ _ _ = (wr,ff)` >>
     `wr = INL ()` by
       (irule tuple_place_source_write_success >>
        qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
        qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
        qpat_assum `stmt_state_rel _ _ _ _ (_ with gas_obs := []) t'` (irule_at Any) >>
        qexistsl_tac [`dty`,`dtv`,`env`] >>
        simp[target_pre_def, vyperTypeSystemTheory.well_typed_target_def] >>
        metis_tac[expr_sim_inv_gas_obs]) >>
     metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env (mid' with gas_obs := [])` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `assignable_type (get_tenv cx) dty` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type] >>
  `0 < type_slot_size dtv` by
    metis_tac[vyperTypeSystemTheory.assignable_type_slot_size_pos] >>
  `!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id mid'.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (qpat_assum `expr_sim_inv cenv cx env (mid' with gas_obs := [])` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[] >> metis_tac[aug_place_store_entry_types]) >>
  `?dw. eval_operand dst t' = SOME dw /\
      place_ptr_rel cenv cx t' (PlaceR p) dw (SOME loc) (Type dty)` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[target_post_def] >> metis_tac[]) >>
  `loc = LocMemory ==> w2n dw + type_memory_size dtv < dimword (:256)` by
    (strip_tac >> irule tuple_place_memory_end_bound >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ _ _ _ (_ with gas_obs := []) t'` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `0 < type_memory_size dtv` by metis_tac[cj 1 type_memory_size_pos] >>
  `type_alloc_ok cenv (lowered_value_type cenv e)` by
    (qpat_assum `assign_alloc_ok _ _ _` mp_tac >>
     qpat_assum `expr_can_mutate _ _` mp_tac >>
     qpat_assum `~(has_length_word _ /\ is_empty_value_expr _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocLimitsTheory.assign_alloc_ok_def]) >>
  `~is_word_type (lowered_value_type cenv e) ==>
      type_memory_size tv < 2 ** 64` by
    (strip_tac >>
     `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     qpat_assum `type_alloc_ok cenv _` mp_tac >>
     qpat_assum `type_memory_bytes cenv _ = type_memory_size tv` mp_tac >>
     qpat_assum `~is_word_type _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocLimitsTheory.type_alloc_ok_def]) >>
  `~is_word_type (lowered_value_type cenv e) ==>
      0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256)` by
    (strip_tac >> conj_tac
     >- (irule assignPlaceLayoutTheory.widening_source_memory_size_pos >>
         metis_tac[]) >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  `is_word_type (lowered_value_type cenv e) = is_word_type dty` by
    metis_tac[arg_type_fits_word_type,
              vyperTypeSystemTheory.type_widens_to_def] >>
  `(is_word_type (lowered_value_type cenv e) \/ dty = lowered_value_type cenv e) ==>
     type_memory_size dtv + 64 < dimword (:256)` by
    (strip_tac
     >- (`type_memory_size dtv = 32` by metis_tac[word_tv_memory_size] >>
         simp[wordsTheory.dimword_def]) >>
     Cases_on `is_word_type dty`
     >- (`type_memory_size dtv = 32` by metis_tac[word_tv_memory_size] >>
         simp[wordsTheory.dimword_def]) >>
     `dtv = tv` by metis_tac[optionTheory.SOME_11] >> metis_tac[]) >>
  `(loc <> LocMemory /\ dty <> lowered_value_type cenv e /\
      ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e))) ==>
      type_alloc_ok cenv dty` by
    (strip_tac >> Cases_on `is_word_type dty`
     >- simp[allocLimitsTheory.type_alloc_ok_def] >>
     `loc = LocStorage \/ loc = LocTransient` by (Cases_on `loc` >> metis_tac[]) >>
     metis_tac[assign_place_caller_normalization_alloc]) >>
  `unwrap_value cenv vv st = (vv_operand vv,st)` by
    (qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `vv0` >>
     simp[compile_snapshot_vv_def, vv_with_type_def, vv_type_def] >>
     Cases_on `is_word_type (lowered_value_type cenv e)` >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     gvs[unwrap_value_def, vv_operand_def, mk_ptr_def,
         contextTheory.compile_ensure_in_memory_def, compileEnvTheory.comp_return_def]) >>
  `su = st /\ op = vv_operand vv` by metis_tac[pairTheory.PAIR_EQ] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!ee ss st u mid p dty dst loc s stv dtv v snap sw sf dw ff. _`
    (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qpat_x_assum `case FST _ of NONE => _ | SOME loc' => _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  disch_then (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (vv_operand _) _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  impl_tac >-
    (simp[] >>
     `ss.cs_next_var <= st.cs_next_var /\ ss.cs_next_id <= st.cs_next_id` by
       metis_tac[ci_mono_def] >>
     `local_ptrs_reserved cenv st` by metis_tac[compiler_ci_mono_reserved] >>
     `~t'.vs_halted` by
       (irule aug_place_marked_path_not_halted >>
        qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
          (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
        metis_tac[]) >>
     simp[] >>
     Cases_on `is_word_type dty` >> fs[] >>
     `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     qexistsl_tac [`aid`,`type_memory_bytes cenv (lowered_value_type cenv e)`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
    (irule vv_post_alloca_frame >>
     qpat_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ t` (irule_at Any) >>
     simp[]) >>
  `MAP FDOM mid'.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[target_post_def, locals_kept_def]) >>
  `alloca_frame cenv (mid with gas_obs := []) ss u
      cenv (mid' with gas_obs := []) t'` by
    (irule target_post_alloca_frame >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[]) >>
  `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) u` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ sr t _ _ u`)) >>
     qexists_tac `sr` >> simp[ci_mono_def] >>
     qpat_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ t` mp_tac >>
     qpat_assum `ci_mono sa sr` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, ci_mono_def] >> metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP u.vs_allocas aid = SOME b` by
    (rpt strip_tac >> irule snapshot_marked_lookup >>
     goal_assum (drule_at (Pat `gas_marked_path _ _ _ t _ (OK u)`)) >>
     qpat_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ t` mp_tac >>
     qpat_x_assum `FLOOKUP s0.vs_allocas _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[vv_post_def]) >>
  `alloca_frame cenv es sa s0 cenv (mid' with gas_obs := []) t'` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ ss u _ _ t'`)) >>
     qexists_tac `ss` >> simp[] >>
     metis_tac[ci_mono_def, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP t'.vs_allocas aid = SOME b` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[target_post_def] >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv ff z` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ st t' _ _ z`)) >>
     qexists_tac `st` >> simp[] >>
     metis_tac[ci_mono_def, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!tail. write_place cx p v (mid' with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    (drule_all place_pointer_write_gas_obs >> simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL ()`,`ff`,`OK z`] >>
  (conj_tac >- simp[gasSummaryTheory.gas_marked_exec_def]) >>
  disj1_tac >> qexists_tac `z` >>
  simp[stmt_post_end_gas_obs] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x z = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sr x /\ not_fresh_at ss x /\ not_fresh_at st x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
     qpat_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ t` mp_tac >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sr x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     qpat_assum `not_fresh_at sr x` mp_tac >>
     qpat_assum `not_fresh_at ss x` mp_tac >>
     qpat_assum `not_fresh_at st x` mp_tac >>
     qpat_assum `lookup_var x s0 = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, target_post_def] >> metis_tac[]) >>
  `gas_marked_path F ctx func s0 (LENGTH marks + LENGTH marks') (OK z)` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> rpt strip_tac >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  `~block_is_terminated sb` by
    (irule endpoint_path_open >>
     goal_assum (drule_at (Pat `gas_marked_path _ _ _ s0 _ (OK z)`)) >>
     simp[] >> metis_tac[ci_mono_def, cs_extends_trans]) >>
  simp[stmt_post_def, stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl] >>
  metis_tac[]
QED

Finalise assign_place_mutating_nonempty_case_with_store
