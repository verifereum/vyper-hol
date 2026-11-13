(* Body typing discharges the memory declaration fragment interface. *)
Theory annAssignPtrDispatch
Ancestors
 annAssignPtrMemory annAssignPtrEmpty annAssignPtrFacts annAssignPtrWord
 bodySimDeclCases bodyExprPreFacts exprSimHyps exprSimHypsDefs bodySim
 bodyPtrPreds bodyPtrDefs memoryLocalRhsProps exprSimSource
 vyperTypeExprSoundness vyperTyping vyperTypeSystem vyperTypeInvariants exprLoweringProps
 allocLimits supportedStmts stmtSimDefs compileEnv vyperInterpreter vyperState
 valueEncoding finite_map
Libs monadsyntax

Theorem body_annassign_memory_ptr:
 !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es d PG.
    body_stmt_safe tops (AnnAssign id typ e) /\
 (!tenv s'' tyv t. tenv = get_tenv cx /\
   lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
     (INL tyv,t) ==> body_expr_ptr_ok cx e) /\
 body_inv tops ctx cenv cx /\
 supported_stmt tops bindings (AnnAssign id typ e) /\
 (!target. supported_stmt_expr_exists
   (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
   occurs_abi_decode_target target tops) /\
 expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
 type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
 stmt_exprs_ok cenv (AnnAssign id typ e) /\
 call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
 ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
 (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
  has_length_word typ /\ is_empty_value_expr e) /\
 (lowered_value_type cenv e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
  arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
   (eval_stmt cx (AnnAssign id typ e)) es
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `FLOOKUP cenv.ce_vars id = NONE` by
   (irule declared_name_unbound >> metis_tac[]) >>
 `well_typed_expr env e /\ assignable_type env.type_defs typ /\
  type_widens_to env.type_defs (expr_type e) typ /\
  id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
 `env.type_defs = get_tenv cx` by
   gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
 `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
   metis_tac[assignable_type_well_formed, well_formed_type_def,
             optionTheory.IS_SOME_EXISTS] >>
 `body_expr_ptr_ok cx e` by (drule_all annassign_ih_ptr >> simp[]) >>
 `supported_expr tops e` by gvs[supported_stmt_def] >>
 `expr_body_pre cenv cx env e es` by (drule_all annassign_rhs_pre_ptr >> simp[]) >>
 `cenv.ce_alloca_locals` by fs[body_inv_def] >>
 `lookup_scopes id es.scopes = NONE` by
   (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
    gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
    res_tac >> gvs[FLOOKUP_DEF]) >>
 `type_memory_bytes cenv typ = type_memory_size tyv` by
   metis_tac[expr_sim_inv_memory_size] >>
 `type_memory_bytes cenv typ < 2 ** 64` by
   gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
 `type_memory_size tyv + 64 < dimword (:256)` by
   metis_tac[allocation_limit_word_room] >>
 Cases_on `has_length_word typ /\ is_empty_value_expr e`
 >- suspend "empty" >>
 suspend "copy"
QED

Resume body_annassign_memory_ptr[empty]:
 irule compile_annassign_empty_stmt_frag_ptr >> gns[] >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >> conj_tac
     >- (drule_all annassign_declared_expr_vv_sim_ptr >> simp[]) >>
     metis_tac[compile_expr_grows]) >>
 rpt gen_tac >> strip_tac >> metis_tac[memory_rhs_empty_eval_destination]
QED

Resume body_annassign_memory_ptr[copy]:
 `supported_program tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
 `expr_type e = typ \/ is_bytestring_type typ` by metis_tac[] >>
 `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv typ` by
   metis_tac[memory_rhs_destination_bound] >>
 drule expr_body_pre_type_evaluates >>
 disch_then (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
 `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by decide_tac >>
 drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
 irule compile_annassign_memory_widen_stmt_frag_ptr >>
 gns[] >> rpt conj_tac
 >>~- ([`expr_sim_ptr _ _ _ _ _ _ _ _ _`],
   rpt gen_tac >> strip_tac >> conj_tac
   >- (drule_all annassign_declared_expr_sim_ptr >> gvs[]) >>
   metis_tac[compile_expr_grows])
 >>~- ([`cs_extends _ _`], metis_tac[compile_expr_grows])
 >>~- ([`value_has_type _ _`],
   rpt gen_tac >> strip_tac >>
   `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
   `value_runtime_typed env typ v /\
    value_runtime_typed env (lowered_value_type cenv e) v` by
     metis_tac[memory_rhs_read_destination_typed, memory_rhs_read_lowered_typed,
               type_widens_to_def] >>
   gvs[value_runtime_typed_def]) >>
 metis_tac[type_widens_to_def, arg_type_fits_bytestring_source]
QED

Finalise body_annassign_memory_ptr
