(* Assignment through an effectful target: evaluate and capture the RHS,
   traverse the target, then store the captured value. *)
Theory bodyMemAssignPlaceSnapshot
Ancestors
  bodyMemoryPreds supportedTargets targetPlaceSim targetPlaceSimMem
  bodyMemAssignSnapshot
  bodyAssignPlace exprSimMemDefs exprSimHypsDefs exprSimHyps
  stmtSimDefs loweringPosts exprLoweringProps exprLowering stmtLowering
  compileEnv assignEffectfulIndexCode fragExec stmtLoweringMono
  bodyMemLoweredSnapshot bodyMemSnapshotTargetFrame
  targetPlaceSimDefs exprSimSubscriptMap exprSimAggregateSource
  exprSimProps exprSimDefs gasOutcome gasSummary gasContext
  vyperState vyperTypeSystem allocLimits
  stmtSimAssignMem bodyMemSnapshotSourceLocation bodyMemSnapshotCapturedFrame
  exprOperandVar memoryLocalRhsProps supportedStmts bodySim
  incompatibleReturnLayout bodyMemSnapshotStages stmtReasonVvMemory
  augAssignPlaceMemoryContinuation exprSimExtract32Counted
  exprSimMemorySource targetPlaceSimCases vyperExprNoControl
  bodyExprPreFacts
  exprSimSource stmtSimAugAssign
  assignPlaceEndpoint
  placeRelayoutSemantic allocLimitsProps
  bodyMemAssignPlaceEmpty bodyMemAssignPlaceCapture bodyMemAssignPlaceStore
  typedCopyCompatibility valueTypingMemoryProps valueEncoding
  bodySimAugPlaceLoad vyperStoragePlaceProvenance stmtSimAugAssignPlaceMemory
  placeMemoryLiveRegion bodyMemoryDefs valueEncodingProps vyperTypeValues
  vyperStorageFrame exprSimWordArgs typedMemoryCopy
  fragGasMode fragGasPath gasCount context venomState loweringStateRelDefs
  stmtSimProps freshWrites stmtSimAssignStorage
Libs monadsyntax

Theorem body_assign_place_snapshot_mem:
  !cx t e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
                 body_base_target_mem_ok cx t) /\
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~immutable_root cx t /\
    expr_can_mutate cenv (target_to_expr t) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es

Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_stmt_safe tops (Assign (BaseTarget t) e)` by
    metis_tac[supported_stmt_body_safe] >>
  drule_then strip_assume_tac assign_place_typing >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_assign_place_rhs_pre] >>
  `target_indices_pre cenv cx env t` by metis_tac[body_assign_place_indices_pre] >>
  `expr_vv_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  `assign_alloc_ok cenv t e` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- suspend "empty" >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule assign_effectful_value_code >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  suspend "nonempty"
QED

Resume body_assign_place_snapshot_mem[nonempty]:
  `ci_mono sa sr` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sr ss` by metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  `ci_mono ss st` by
    metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono st su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su sb` by
    (qpat_x_assum `case FST (SND r) of NONE => _ | SOME loc => _` mp_tac >>
     Cases_on `FST (SND r)` >> simp[] >> strip_tac >>
     metis_tac[ci_mono_stmt_helpers, ci_mono_emit_void, pairTheory.SND]) >>
  `fn_has_code sa sr func /\ fn_has_code sr ss func /\
   fn_has_code ss st func /\ fn_has_code st su func /\
   fn_has_code su sb func` by
    metis_tac[ci_mono_def, fn_has_code_split, cs_extends_trans] >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  irule gas_outcome_bind_result_exec >>
  qexistsl_tac [
    `\res ee rr. expr_exit res rr`,
    `\res ee u. ?pv. res = INL pv /\
       vv_post ctx func cenv cx e es sa sr s0 ee pv vv0 u /\
       vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee pv vv0 u /\
       u.vs_current_bb = sr.cs_current_bb /\
       u.vs_inst_idx = LENGTH sr.cs_current_insts /\
       alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next`] >>
  conj_tac
  >- (BETA_TAC >> Cases >- simp[exprSimDefsTheory.expr_exit_INL] >>
      rpt gen_tac >> strip_tac >> qexists_tac `y` >>
      simp[stmt_exit_def] >> rpt gen_tac >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  conj_tac
  >- (qx_genl_tac [`marks`, `raw`, `mid`, `rs`] >>
      BETA_TAC >> strip_tac >>
      qpat_x_assum `INL _ = INL _` (assume_tac o SRULE []) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      suspend "snapshot") >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then irule >> simp[] >>
  metis_tac[expr_body_pre_vv_gas_admissible]
QED

Resume body_assign_place_snapshot_mem[empty]:
  qpat_x_assum `has_length_word (expr_type e) /\ is_empty_value_expr e`
    strip_assume_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  mp_tac (Q.SPECL [`cx`,`env`,`e`,`es`] memory_rhs_empty_read_total) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `body_base_target_mem_ok cx t` by
    (qpat_x_assum `(do r <- eval_expr cx e; read_result cx r od) es = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]) >>
  `target_sim_mem ctx func cenv cx env t es` by
    metis_tac[body_target_sim_mem, target_pre_def] >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    metis_tac[memory_rhs_read_destination_typed, memory_rhs_runtime_layout] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  drule_all compile_assign_place_empty_stmt_frag_mem >> simp[]
QED

Resume body_assign_place_snapshot_mem[snapshot]:
  markerLib.RESUME_TAC >>
  rename1 `vv_post ctx func cenv cx e es sa sr s0 (mid with gas_obs := []) raw vv0 rs` >>
  `?v. read_result cx raw (mid with gas_obs := []) =
      (INL v,mid with gas_obs := [])` by metis_tac[vv_post_materialises] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,mid with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `(do rv <- eval_expr cx e; read_result cx rv od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by simp[bind_def] >>
  `body_base_target_mem_ok cx t` by
    (first_x_assum (qspecl_then
       [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
        `raw`,`mid with gas_obs := []`,`mid with gas_obs := []`,
        `v`,`mid with gas_obs := []`] mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval_result] >>
  `supported_expr tops e /\ supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by
    fs[supported_stmt_def, supported_assignment_def, body_inv_def] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    metis_tac[memory_rhs_read_lowered_typed] >>
  `?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    value_has_type stv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[memory_rhs_runtime_layout] >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[memory_rhs_read_destination_typed, memory_rhs_runtime_layout] >>
  suspend "capture"
QED

Resume body_assign_place_snapshot_mem[capture]:
  markerLib.RESUME_TAC >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `eval_expr cx e _ = _`
       (mp_tac o MATCH_MP
         vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  `~rs.vs_halted` by
    (irule aug_place_marked_path_not_halted >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  `type_alloc_ok cenv (lowered_value_type cenv e)` by
    fs[assign_alloc_ok_def] >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    value_has_type etv v` by
    metis_tac[memory_rhs_read_annotation_typed, memory_rhs_runtime_layout] >>
  drule_all assign_place_capture_mem >>
  disch_then (qx_choose_then `snap` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) snap` by
    fs[vv_post_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    metis_tac[type_widens_to_trans] >>
  `assignable_type (get_tenv cx) (lowered_value_type cenv e)` by
    metis_tac[arg_type_fits_source_assignable, type_widens_to_def,
              well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `unwrap_value cenv vv st = (vv_operand vv,st)` by
    metis_tac[snapshot_saved_representation] >>
  qpat_x_assum `unwrap_value _ _ _ = (op,su)` mp_tac >>
  simp[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  irule gas_outcome_zero_prefix_any >> qexists_tac `snap` >> simp[] >>
  suspend "target_prefix"
QED

Resume body_assign_place_snapshot_mem[target_prefix]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel ctx func cenv cx mid snap` by
    fs[stmt_state_rel_gas_obs] >>
  `target_sim_mem ctx func cenv cx env t (mid with gas_obs := [])` by
    metis_tac[body_target_sim_mem, target_pre_def] >>
  `local_ptrs_reserved cenv ss` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!tail. read_result cx raw (mid with gas_obs := tail) =
      (INL v,mid with gas_obs := tail)` by
    (drule read_result_gas_obs >> simp[]) >>
  `gas_admissible
    (vyperState$bind (eval_target_place cx t) (\p. write_place cx p v))
    (stmt_res_ok lctx) (mid with gas_obs := [])` by
    (rw[gas_admissible_def] >>
     drule gas_admissible_result >> disch_then irule >>
     drule gas_marked_exec_observation >>
     disch_then (qspec_then `gs` assume_tac) >>
     qexistsl_tac [`ee`, `gas_explicit marks s0.vs_gas_readings ++ gs`] >>
     gnvs[] >> simp[Once vyperInterpreterTheory.evaluate_def, bind_def] >>
     fs[bind_def]) >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok
      (mid with gas_obs := [])` by metis_tac[empty_target_admissible] >>
  `gas_marked_exec T (ctx,func) (read_result cx raw)
      (mid with gas_obs := [],snap) [] (INL v) mid (OK snap)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[fragGasPathMemTheory.gas_path_mem_rules]) >>
  irule extract32_outcome_read_prefix >> goal_assum (drule_at Any) >> simp[] >>
  irule aug_place_target_mem_continuation >> simp[] >> (conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) rr` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])) >>
  qexistsl_tac [`cenv`,`env`,`r`,`ss`,`st`,`dty`] >> simp[] >>
  suspend "target"
QED

Resume body_assign_place_snapshot_mem[target]:
  markerLib.RESUME_TAC >>
  qx_genl_tac [`p`,`after`,`target`,`target_marks`] >> strip_tac >>
  `~target.vs_halted` by metis_tac[aug_place_marked_path_not_halted] >>
  `eval_target_place cx t
    (mid with gas_obs := gas_explicit target_marks snap.vs_gas_readings ++ after.gas_obs) =
    (INL p,after)` by
    (qpat_x_assum `!tail. eval_target_place _ _ _ = _`
      (qspec_then `after.gas_obs` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env after` by
    (irule aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >> simp[] >>
     metis_tac[expr_sim_inv_gas_obs]) >>
  `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id after.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    metis_tac[aug_place_entry_type_agrees] >>
  `gas_admissible (write_place cx p v) (stmt_res_ok lctx) after` by
    (irule (BETA_RULE (Q.INST [`k` |-> `\p. write_place cx p v`]
       empty_store_admissible)) >>
     qexistsl_tac [`t`,`mid with gas_obs := []`,
                  `gas_explicit target_marks snap.vs_gas_readings`] >> simp[]) >>
  `?dst loc. r = (dst,SOME loc,SOME (ValPT dty)) /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)` by
    (PairCases_on `r` >> fs[target_post_def, exprLoweringTheory.value_type_place_def] >>
     Cases_on `p` >> fs[place_ptr_rel_def, slot_loc_def] >>
     Cases_on `b` >> gvs[slot_loc_def]) >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  suspend "transport"
QED

Resume body_assign_place_snapshot_mem[transport]:
  markerLib.RESUME_TAC >>
  `ss.cs_next_var <= st.cs_next_var /\ ss.cs_next_id <= st.cs_next_id` by
    fs[ci_mono_def] >>
  `?w. eval_operand dst target = SOME w /\
    place_ptr_rel cenv cx target (PlaceR p) w (SOME loc) (Type dty)` by
    fs[target_post_def] >>
  `stmt_state_rel ctx func cenv cx after target` by fs[target_post_def] >>
  `MAP FDOM mid.scopes = MAP FDOM after.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >>
     simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM after.scopes` by simp[] >>
  `local_ptrs_reserved cenv st` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `well_formed_type_value stv /\ well_formed_type_value dtv /\
   val_wf stv v /\ val_wf dtv v` by
    metis_tac[evaluate_type_well_formed_type_value, value_has_type_memory_wf] >>
  `0 < type_memory_size stv` by
    metis_tac[assignable_type_slot_size_pos, type_memory_size_pos] >>
  `!x. vv_operand vv = Var x \/ dst = Var x ==> not_fresh_at st x` by
    (fs[target_post_def] >> metis_tac[not_fresh_at_mono, ci_mono_def,
                                   not_fresh_at_mono]) >>
  `is_word_type dty ==> expr_val_rel cx dty v (vv_operand vv) target` by
    (strip_tac >>
     `lowered_value_type cenv e = dty` by metis_tac[type_widens_to_word] >>
     gvs[] >> drule_all snapshot_target_scalar_frame >> simp[ci_mono_def]) >>
  `~is_word_type dty ==>
    ~is_word_type (lowered_value_type cenv e) /\
    vv_at cenv cx (lowered_value_type cenv e) sr st after (Value v) vv target /\
    vv_location vv = SOME LocMemory /\
    ?sw. eval_operand (vv_operand vv) target = SOME sw /\
      val_in_memory stv v (w2n sw) target.vs_memory /\
      w2n sw + type_memory_size stv <= target.vs_alloca_next` by
    suspend "owned_target" >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `loc <> LocMemory /\ dty <> lowered_value_type cenv e /\
    ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
    type_memory_size dtv < dimword (:256)` by
    (strip_tac >>
     `~is_word_type dty` by metis_tac[type_widens_to_word] >>
     `target_store_place cenv t = SOME (SOME (ValPT dty))` by
       (drule compile_get_target_ptr_store_place >> simp[] >> metis_tac[]) >>
     fs[assign_alloc_ok_def] >>
     CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> decide_tac) >>
  Cases_on `write_place cx p v after` >>
  rename1 `write_place cx p v after = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ff`,`after.gas_obs`] >> simp[]) >>
  `res = INL ()` by suspend "normal_write" >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  `loc = LocMemory ==> w2n w + type_memory_size dtv <= target.vs_alloca_next` by
    (strip_tac >> gvs[] >> drule_all memory_place_live_region >> strip_tac >>
     drule_all body_local_region_frontier >> decide_tac) >>
  `!sw. eval_operand (vv_operand vv) target = SOME sw ==>
    (@sw. eval_operand (vv_operand vv) target = SOME sw) = sw` by
    (rpt strip_tac >> irule SELECT_UNIQUE >> simp[EQ_SYM_EQ]) >>
  `?z. gas_marked_path T ctx func target 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x target) /\
    (!aid b. FLOOKUP target.vs_allocas aid = SOME b ==>
      FLOOKUP z.vs_allocas aid = SOME b) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ target.vs_alloca_next <= z.vs_alloca_next` by
    (mp_tac (Q.INST [`ce` |-> `cenv`, `dst` |-> `dst`, `loc` |-> `loc`,
       `saved` |-> `vv`, `dty` |-> `dty`, `sty` |-> `lowered_value_type cenv e`,
       `sa` |-> `st`, `sb` |-> `sb`, `cx` |-> `cx`, `stv` |-> `stv`,
       `dtv` |-> `dtv`, `v` |-> `v`, `s` |-> `target`, `origin` |-> `sr`,
       `ee` |-> `after`, `sw` |-> `@sw. eval_operand (vv_operand vv) target = SOME sw`,
       `w` |-> `w`, `p` |-> `p`, `env` |-> `env`, `ctx` |-> `ctx`,
       `func` |-> `func`, `ff` |-> `ff`] (SPEC_ALL assign_place_captured_store_mem)) >>
     (impl_tac >- (fs[] >> rpt conj_tac >> rpt strip_tac >> fs[] >>
       metis_tac[])) >> simp[]) >>
  suspend "finish"
QED

Resume body_assign_place_snapshot_mem[owned_target]:
  markerLib.RESUME_TAC >> strip_tac >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[return_source_word_widens_eq] >>
  fs[] >> drule_all snapshot_nonword_slices >> strip_tac >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `val_wf stv v` by metis_tac[value_has_type_memory_wf] >>
  `vv_own cenv cx (lowered_value_type cenv e) sr ss mid (Value v)
     (LocatedValue (lowered_value_type cenv e) (mk_ptr buf.buf_operand LocMemory)) snap` by
    (qpat_x_assum `vv_own _ _ _ _ _ (_ with gas_obs := []) (Value v) _ snap` mp_tac >>
     simp[vv_own_def, mk_ptr_def, read_result_def, return_def]) >>
  rename1 `val_in_memory stv v (w2n saved_word) snap.vs_memory` >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at ss x) /\
   (!l. buf.buf_operand <> Label l) /\
   eval_operand buf.buf_operand snap = SOME saved_word` by
    fs[vv_operand_def, mk_ptr_def] >>
  drule_all snapshot_captured_memory_target >> strip_tac >>
  simp[vv_operand_def, vv_location_def, mk_ptr_def] >>
  qexists_tac `saved_word` >> fs[target_post_def, ci_mono_def] >> decide_tac
QED

Resume body_assign_place_snapshot_mem[normal_write]:
  markerLib.RESUME_TAC >>
  (Cases_on `p`
  >- (gvs[place_ptr_rel_def] >>
      rename1 `write_place cx (StoragePlace tr slot dtv) v after = _` >>
      `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
      mp_tac (Q.SPECL [`cx`,`tr`,`slot`,`dtv`,`v`,`after`]
        write_storage_slot_succeeds) >> simp[] >>
      qpat_x_assum `write_place _ _ _ _ = _`
        (fn th => simp[REWRITE_RULE [write_place_def] th]))
  >- (rename1 `MemoryPlace id path` >>
      `?entry. lookup_scopes id after.scopes = SOME entry` by
        (Cases_on `lookup_scopes id after.scopes`
         >- fs[target_post_def, place_readable_def, read_place_def,
               get_scopes_def, bind_def, lift_option_type_def,
               lift_sum_def, return_def, raise_def] >> simp[]) >>
      drule_all empty_memory_write_success >> simp[]) >>
  qpat_x_assum `place_ptr_rel _ _ _ (PlaceR (ImmutablePlace _ _ _)) _ _ _` mp_tac >>
  simp[place_ptr_rel_def])
QED

Resume body_assign_place_snapshot_mem[finish]:
  markerLib.RESUME_TAC >>
  `!tail. write_place cx p v (after with gas_obs := tail) =
    (INL (),ff with gas_obs := tail)` by
    (Cases_on `p`
     >- (qpat_x_assum `write_place _ _ _ _ = _`
           (fn th => simp_tac std_ss [write_place_def,
             write_storage_slot_gas_obs, REWRITE_RULE [write_place_def] th]))
     >- (drule aug_place_memory_write_gas_obs >> simp[]) >>
     qpat_x_assum `place_ptr_rel _ _ _ (PlaceR (ImmutablePlace _ _ _)) _ _ _` mp_tac >>
     simp[place_ptr_rel_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x z = SOME w` by
    (fs[target_post_def, vv_post_def] >>
     metis_tac[compiler_ci_mono_not_fresh, ci_mono_def, cs_extends_trans]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP z.vs_allocas aid = SOME b` by
    (fs[target_post_def, vv_post_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sb z` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def] >> decide_tac) >>
  `gas_marked_path F ctx func s0
    (LENGTH marks + LENGTH target_marks) (OK z)` by
    (simp[gas_marked_path_def] >>
     `gas_path ctx func s0 (LENGTH marks) (OK rs)` by
       (fs[gas_marked_exec_def] >> metis_tac[gas_marked_path_exec]) >>
     `gas_path ctx func rs 0 (OK snap) /\
      gas_path ctx func snap (LENGTH target_marks) (OK target) /\
      gas_path ctx func target 0 (OK z)` by
       metis_tac[gas_marked_path_exec] >>
     `gas_path ctx func s0 (LENGTH marks) (OK snap)` by
       (irule (SRULE [] (Q.INST [`m` |-> `0`] gas_path_then)) >>
        qexists_tac `rs` >> simp[]) >>
     `gas_path ctx func snap (LENGTH target_marks) (OK z)` by
       (irule (SRULE [] (Q.INST [`m` |-> `0`] gas_path_then)) >>
        qexists_tac `target` >> simp[]) >>
     irule gas_path_then >> qexists_tac `snap` >> simp[]) >>
  `~block_is_terminated sb` by
    (irule endpoint_path_open >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[ci_mono_def, cs_extends_trans]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`,`ff`,`OK z`] >>
  simp[stmt_lands_def, cenv_top_ext_def, stmt_state_rel_gas_obs] >>
  fs[target_post_def] >> decide_tac
QED

Finalise body_assign_place_snapshot_mem
