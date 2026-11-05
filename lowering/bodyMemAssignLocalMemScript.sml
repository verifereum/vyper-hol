(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a local held in memory, the value at its lowered type or a bytestring that fits
   (S1's body_assign_local_memory). *)
Theory bodyMemAssignLocalMem
Ancestors
  bodyMemoryPreds bodySim bodyExprPreFacts memoryLocalRhsProps
  bodyRhsRoomMemory exprSimAggregateLayout vyperTypeArgFits
  supportedStmtTraverse supportedStmts supportedExprs vyperTypeSystem
  vyperTypeEnv exprSimHyps exprSimHypsDefs exprSimDefs gasContext
  vyperTypeCallGraph vyperTypeInvariants gasOutcome exprSimMemDefs
Libs
  monadsyntax

Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]) >>
  simp[] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem assign_local_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id e env' ty.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    0 < type_memory_bytes cenv ty
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `assignable_type env.type_defs ty` by
    (gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     Cases_on `type_place_target env (NameTarget id)` >> gvs[] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type]) >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

Theorem assign_local_memory_type_cases[local]:
  !cenv e ty.
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    expr_type e = ty \/ is_bytestring_type ty
Proof
  metis_tac[]
QED

Theorem body_assign_local_memory_read[local]:
  !cenv cx env e es tops id ty tyv v es1 entry.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_program tops /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    get_module_code cx NONE = SOME tops /\
    FLOOKUP env.var_types id = SOME ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    entry.type = tyv /\ value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `entry.type = tyv` by metis_tac[memory_rhs_read_local_type] >>
  simp[] >> irule memory_rhs_read_destination_footprint >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cx`, `env`, `es`, `es1`, `tops`, `ty`] >> simp[]
QED

Theorem assign_local_memory_sizes[local]:
  !cenv cx env es ret_ty id e env' ty tops.
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty /\
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    0 < type_memory_bytes cenv ty /\ type_memory_bytes cenv ty < 2 ** 64 /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_bytes cenv ty` by
    metis_tac[assign_local_memory_bytes_pos] >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    metis_tac[locals_alloc_ok_def] >>
  metis_tac[memory_rhs_destination_bound]
QED

Theorem assign_local_rhs_located_mem[local]:
  !tops ctx func c cx env e es ltv etv.
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

Theorem body_assign_local_memory_mem:
  !cx id e ty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED
