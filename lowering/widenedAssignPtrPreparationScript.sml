(* Static classification and compiler boundaries for widened local writes. *)
Theory widenedAssignPtrPreparation
Ancestors assignBasePtrLocalBodyFacts exprSimIfExpCompat exprSimHypsDefs
  exprSimHyps exprSimDefs exprSimSource exprSimProps bodyExprPreFacts
  bodySim vyperTypeSystem vyperTypeInvariants stmtSimAugAssign
  stmtLowering stmtSimAssignMem stmtSimAssignStore
  context compileEnv externalEntryShape exprLoweringProps
  exprSimUnwrap fragExec finite_map list

Theorem widened_assignment_internal_call:
  expr_body_pre ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?ann fid args drv. e = Call ann (IntCall fid) args drv
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
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem widened_assignment_code:
  stmt_env ce lctx rty (Assign (BaseTarget (NameTarget id)) e) sa = (c,sf) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME ty /\ ~is_word_type ty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  fn_has_code sa sf fn ==>
  c = ce /\ ?vv sm sb op.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,sb) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) ty
      (lowered_value_type ce e) (type_memory_bytes ce ty) sb = ((),sf) /\
    fn_has_code sa sm fn /\ fn_has_code sa sb fn /\ fn_has_code sb sf fn
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` >>
  drule compile_get_target_ptr_local >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, exprLoweringTheory.expr_can_mutate_def,
     target_to_expr_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  Cases_on `unwrap_value ce vv sm` >>
  rename1 `unwrap_value _ _ _ = (op,sb)` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[unwrap_value_extends] >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sb sf` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     metis_tac[compile_assign_value_labels, pairTheory.SND]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sf fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code sa sm fn` by metis_tac[fn_has_code_split] >> gvs[]
QED
