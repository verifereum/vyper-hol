(* Source replay and current immutable readiness for the scalar continuation. *)
Theory immutableAugAssignSourceContinuation
Ancestors
  bodyImmutableAugAssignFacts bodyImmutableAugAssignExec augAssignPlaceSourceMemory
  augAssignPlaceSourcePrefix vyperTypeEnv vyperTypeInvariants vyperTypeValues
  stmtSimAugAssignPlaceMemory stmtSimAugAssign gasContext vyperInterpreter
  loweringPosts vyperState

Theorem immutable_augassign_root_replay:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (tv,iv) ==>
  !gs. eval_target_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
         (INL (ImmutablePlace src id []),es with gas_obs := gs) /\
    read_place cx (ImmutablePlace src id []) (es with gas_obs := gs) =
         (INL iv,es with gas_obs := gs) /\
    place_type_value cx (ImmutablePlace src id []) (es with gas_obs := gs) =
         (INL tv,es with gas_obs := gs)
Proof
  strip_tac >> Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  drule_all immutable_augassign_prefix_obs >> simp[]
QED

Theorem immutable_augassign_current_root:
  expr_sim_inv cenv cx env ee /\
  FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?imms a. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,a) /\
    value_has_type tv a /\ well_formed_type_value tv
Proof
  strip_tac >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >> metis_tac[]) >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem immutable_augassign_source_replay:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (tv,iv) ==>
  !gs. eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
    (es with gas_obs := gs) =
    vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (\rhs. vyperState$bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop iv rhs)) (write_place cx (ImmutablePlace src id [])))
      (es with gas_obs := gs)
Proof
  strip_tac >> drule_all immutable_augassign_root_replay >> strip_tac >>
  gen_tac >>
  qpat_x_assum `!gs. eval_target_place _ _ _ = _ /\ _`
    (qspec_then `gs` strip_assume_tac) >>
  drule_all immutable_augassign_forced >> simp[ignore_bind_def, bind_assoc, SF ETA_ss]
QED

Theorem immutable_augassign_rhs_source:
  expr_body_pre cenv cx env e es /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv cur /\ word_value cur /\
  gas_admissible
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (\rhs. vyperState$bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur rhs)) (write_place cx (ImmutablePlace src id []))))
    (stmt_res_ok lctx) es /\
  vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL rhs,ee) ==>
  word_value rhs /\ expr_sim_inv cenv cx env ee /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE) [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type tv v)
Proof
  strip_tac >> drule_all aug_place_rhs_typed_memory_source >> strip_tac >>
  drule stmtSimAugAssignPlaceTheory.aug_place_typing >> strip_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `gas_admissible (vyperState$bind a k) _ es` >>
  Cases_on `k rhs ee` >> rename1 `k rhs ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >> disch_then (qspec_then `gs` mp_tac) >>
     simp[bind_def, Abbr `a`] >> metis_tac[]) >>
  irule aug_place_bop_write_result_ok >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl [`ff`, `ImmutablePlace src id []`] >>
  `!bs. cur <> BytesV bs` by (Cases_on `cur` >> gvs[loweringSliceTheory.word_value_def]) >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs ee =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  simp[] >>
  qpat_x_assum `k rhs ee = _` mp_tac >>
  simp[Abbr `k`, bind_def, lift_sum_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur rhs` >> simp[return_def, raise_def]
QED
