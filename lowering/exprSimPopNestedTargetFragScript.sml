(*
 * Pop on a nested target: pop_nested_expr_target_frag, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedTargetFrag
Ancestors
  exprSimPopNestedBase targetPlaceSimCasesBase exprSimHypsDefs allocLimits
  supportedExprTraverse
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* The static half of expr_body_pre holds of every index of a typed target
   whose static checks hold, so target_indices_pre does. *)
Theorem target_indices_pre_static[local]:
  !bt vt cenv cx env.
    type_place_target env bt = SOME vt /\ byte_widths_target bt /\
    alloc_limits_target cenv bt /\ int_calls_target bt = [] /\
    call_evaluation_safe cx [] /\
    ~supported_target_exists expr_evm_run_root bt /\
    ~supported_target_exists call_operands_effect_root bt /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    target_indices_pre cenv cx env bt
Proof
  recInduct base_assignment_target_induct >>
  rw[target_indices_pre_def, type_place_target_SubscriptTarget,
     type_place_target_AttributeTarget, byte_widths_expr_def,
     alloc_limits_expr_def, supported_expr_exists_def, int_calls_expr_def]
  >- metis_tac[]
  >- gvs[expr_body_pre_def, expr_has_evm_run_def]
  >- metis_tac[]
QED

(* The target's fragment judgment at the expression level: target_case_all
   gives target_sim from the indices' judgments (expr_ok, below the pop's
   size) and target_pre (static, from expr_sim_pre). *)
Theorem pop_nested_expr_target_frag:
  !cenv ann bt ctx func cx env es.
    expr_sim_below cenv (expr_size (Pop ann bt)) /\
    expr_sim_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  rpt strip_tac >> irule pop_target_frag_of_sim >>
  gvs[expr_sim_pre_def, int_calls_expr_def] >>
  `target_case T ctx func cenv cx bt` by
    (irule target_case_all >> irule target_idx_case_ok >>
     rw[] >> fs[expr_sim_below_def] >> first_x_assum irule >>
     imp_res_tac nested_pop_index_size >> simp[expr_size_def]) >>
  fs[target_case_def] >> first_x_assum irule >>
  simp[target_pre_def] >>
  gvs[well_typed_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
      expr_has_evm_run_def, supported_expr_exists_def,
      call_operands_effect_root_def] >>
  irule target_indices_pre_static >> simp[] >> metis_tac[]
QED
