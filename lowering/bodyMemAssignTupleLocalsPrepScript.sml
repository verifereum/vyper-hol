(* Source and typing boundaries for the memory-counted tuple-local case. *)
Theory bodyMemAssignTupleLocalsPrep
Ancestors
  bodyMemAssignTupleLocalsFacts bodyMemoryPreds bodySim bodyExprPreFacts
  bodyRhsRoomMemory exprSimAggregateLayout vyperTypeArgFits
  supportedStmtTraverse supportedStmts supportedExprs vyperTypeSystem
  vyperTypeEnv exprSimHyps exprSimHypsDefs exprSimDefs gasContext
  vyperTypeCallGraph vyperTypeInvariants gasOutcome exprSimMemDefs
  stmtSimProps valueEncoding localPtrsProps exprLoweringProps loweringPosts
  venomState venomExecSemantics compileEnv finite_map list vyperLookup
  loweringSlice bodyMemoryDefs stmtSimAssignStore allocLimits
  valueTypingMemoryProps stmtSimDefs vyperState stmtLowering
  exprOperandVar freshWrites exprSimSource gasOracleReplay
  vyperTypeCallStackSoundness memoryLocalRhsProps stmtSimAugAssign stmtSimDeclStore
Libs
  monadsyntax

(* Restatement of S1 bodySimStmtCases.body_assign_tuple_rhs_pre [local]. *)
Theorem body_assign_tuple_rhs_pre:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

(* Restatement of S1 bodySimStmtCases.assign_tuple_locals_bytes_pos [local]. *)
Theorem assign_tuple_locals_bytes_pos:
  !cenv cx env es ret_ty ids e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' ==>
    EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
                     0 < type_memory_bytes cenv ty) ids
Proof
  rpt strip_tac >>
  `?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty)
           (MAP (BaseTarget o NameTarget) ids) tys /\
         assignable_type env.type_defs (TupleT tys)` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
         AllCaseEqs()] >> metis_tac[]) >>
  `EVERY (assignable_type env.type_defs) tys` by fs[assignable_type_def, EVERY_MEM] >>
  rw[EVERY_EL] >>
  `n < LENGTH tys /\
   well_typed_atarget env (BaseTarget (NameTarget (EL n ids))) (EL n tys)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `n` mp_tac) >>
     simp[EL_MAP]) >>
  `ty = EL n tys` by
    gvs[well_typed_atarget_def, well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_NameTarget, AllCaseEqs()] >>
  `assignable_type env.type_defs ty` by metis_tac[EVERY_EL] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

(* Restatement of S1 bodySimStmtCases.tuple_staging_bound [local]. *)
Theorem tuple_staging_bound:
  !cenv cx env es g e tys tvs.
    expr_sim_inv cenv cx env es /\
    stmt_exprs_ok cenv (Assign (TupleTarget g) e) /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    is_memory_view e ==>
    type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (TupleT tys) < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_size (TupleTV tvs) + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >> decide_tac
QED

(* The type/arity information used by the lowering code decomposition. *)
Theorem tuple_locals_source_types:
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty
    (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' ==>
  ?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    LENGTH tys = LENGTH ids /\
    !i. i < LENGTH ids ==> FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
      LIST_REL_EL_EQN, EL_MAP, well_typed_target_def,
      well_typed_expr_def, AllCaseEqs()]
QED

(* Non-word RHS outcome, retaining room only for a located memory view.
   Same interface as S3 bodyMemAssignLocalMem.assign_local_rhs_located_mem. *)
Theorem tuple_rhs_located_mem:
  !tops ctx func c cx env e es ltv etv.
    post_value_type c e = expr_type e /\
    body_inv tops ctx c cx /\ expr_body_pre c cx env e es /\
    body_expr_mem_ok cx e /\ ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    type_memory_bytes c (expr_type e) = type_memory_size etv /\
    type_memory_size etv < 2 ** 64 /\ 0 < type_memory_size ltv ==>
    !sa sm sb vv op s0.
      compile_expr c (expr_type e) e sa = (vv, sm) /\
      unwrap_value c vv sm = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved c sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func c cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func c cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          (vv_location vv = SOME LocMemory ==>
           !sw. eval_operand op t = SOME sw ==>
                w2n sw + type_memory_size ltv <= t.vs_alloca_next) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  drule expr_sim_mem_room >>
  disch_then (qspecl_then [`sa`, `sm`, `sb`, `vv`, `op`, `s0`] mp_tac) >>
  impl_tac >- (rpt strip_tac >> gvs[]) >> strip_tac >>
  irule gas_outcome_post_mono >>
  first_x_assum (irule_at (Pos last)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rpt strip_tac >> qpat_x_assum `vv_location _ = _ ==> _` drule >>
  disch_then drule >> strip_tac >> decide_tac
QED

(* Restatement of S1 bodySimStmtCases.tuple_target_local_ptr [local]. *)
Theorem tuple_target_local_ptr:
  !cenv cx env es id ty tv.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    FLOOKUP env.var_types id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    ?p sz vt.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME vt /\
      if is_word_type ty then is_word_type vt
      else
        (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
        type_memory_bytes cenv ty = type_memory_size tv /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
              type_memory_bytes cenv vt = type_memory_size vtv /\
              0 < type_memory_size vtv /\
              type_memory_size vtv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_local] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qexistsl_tac [`p`, `sz`, `ty`] >> simp[] >>
  Cases_on `is_word_type ty` >> simp[] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

(* Restatement of S1 bodySimStmtCases.tuple_target_local_lays_out [local]. *)
Theorem tuple_target_local_lays_out:
  !cenv cx env es1 id ty tv v entry.
    expr_sim_inv cenv cx env es1 /\ FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    lookup_scopes id es1.scopes = SOME entry ==>
    if is_word_type ty then store_lays_out tv entry.type v
    else
      ?vt. cenv.ce_var_type id = SOME vt /\
           evaluate_type (get_tenv cx) vt = SOME entry.type /\
           value_has_type entry.type v
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `entry.type = tv` by metis_tac[optionTheory.SOME_11] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  IF_CASES_TAC >> simp[] >> metis_tac[store_lays_out_typed]
QED
