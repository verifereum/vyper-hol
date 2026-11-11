(* Static and live-local interfaces for widened assignment copies. *)
Theory widenedAssignmentPreparationMem
Ancestors
  bodyMemAssignLocalMem widenedDeclareContinuationMem localCopyDestinationMem
  exprSimHyps exprSimIfExpCompat memoryLocalRhsProps vyperTypeSystem
  bodyExprPreFacts exprSimHypsDefs exprSimDefs exprSimSource exprSimProps
  vyperTypeInvariants gasSummary stmtSimAugAssign
Libs monadsyntax

Theorem arg_type_fits_antisymmetric[local]:
  (!t u. arg_type_fits t u ==> arg_type_fits u t ==> t = u) /\
  (!ts us. arg_types_fit ts us ==> arg_types_fit us ts ==> ts = us)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def] >> gvs[arg_type_fits_def] >> metis_tac[]
QED

Theorem widened_assignment_rhs_classify:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  supported_expr tops e /\ type_widens_to env.type_defs (expr_type e) ty /\
  ~is_word_type ty /\
  (expr_type e = ty \/ lowered_value_type ce e = ty \/ is_bytestring_type ty \/
   has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?ann fid args drv. e = Call ann (IntCall fid) args drv /\
    ~is_word_type ann /\ ~is_bytestring_type ann /\ ~is_bytestring_type ty /\
    lowered_value_type ce e <> ann /\ lowered_value_type ce e <> ty /\
    type_widens_to env.type_defs ann ty
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  rename1 `expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es` >>
  `arg_type_fits (lowered_value_type ce (Call ann (IntCall fid) args drv)) ann` by
    metis_tac[exprSimHypsTheory.ifexp_body_pre_intcall_physical] >>
  gvs[vyperASTTheory.expr_type_def, stmtLoweringTheory.is_empty_value_expr_def,
      type_widens_to_def] >>
  metis_tac[compileEnvTheory.arg_type_fits_bytestring_source,
            arg_type_fits_antisymmetric]
QED

Theorem widened_assignment_live_destination:
  expr_body_pre ce cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  gas_marked_exec T (ctx,fn)
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK t) /\
  stmt_state_rel ctx fn ce cx (ee with gas_obs := []) t /\
  find_containing_scope id ee.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  entry.type = dtv /\ ?dw. lookup_var p t = SOME dw /\
    local_region ce ee.scopes t id (w2n dw) sz /\ type_memory_size dtv <= sz /\
    w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
    w2n dw + type_memory_size dtv < dimword(:256)
Proof
  strip_tac >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `entry.type = dtv` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     irule memory_rhs_read_local_type >>
     qexistsl_tac [`ce`, `cx`, `e`, `env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`, `id`, `ty`, `v`] >> simp[] >>
     gvs[ETA_THM, vyperStateTheory.bind_def]) >>
  `lookup_scopes id (ee with gas_obs := []).scopes = SOME entry` by simp[] >>
  `?dw. lookup_var p t = SOME dw` by
    (drule_all stmtSimAugAssignTheory.local_word_pointer_live >> simp[]) >>
  `type_memory_size dtv <= type_memory_size entry.type` by simp[] >>
  drule_all local_copy_destination_region >> simp[] >> metis_tac[]
QED
