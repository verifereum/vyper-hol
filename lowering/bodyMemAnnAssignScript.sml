(* Memory case of the body induction (bodyMemory's body_mem_mutual): annotated
   assignment (declaration).  As bodySimDeclCases' body_annassign_case, by
   the declared type: a word (bodyDeclWordMemory), the empty value of a type
   with a length word (bodyDeclEmptyMemory), a bytestring
   (bodyDeclBytesMemory), any other type copied from a value of the type
   itself (bodyDeclCopyMemory), or a widened aggregate call
   (bodyMemAnnAssignWidened, HELD).  A supported declaration copies a value
   of the declared type, a word, or a bytestring (supported_copy_types), so
   there are no other cases. *)
Theory bodyMemAnnAssign
Ancestors
  supportedExprTraverse allocLimitsProps
  bodyMemoryPreds bodyDeclWordMemory bodyDeclCopyMemory bodyDeclEmptyMemory
  bodyDeclBytesMemory bodyMemAnnAssignWidened bodySimDeclCases
  memoryLocalRhsProps bodyExprPreFacts exprSimHyps exprSimSource
  exprSimAggregateLayout stmtSimDeclStore stmtSimReturn stmtSimAssign
  allocLimits supportedTypes typedCopyMetadata gasContext bodySim
  supportedStmtTraverse vyperTypeCallGraph supportedStmts exprSimHypsDefs
  vyperTypeInvariants vyperTypeExprSoundness
  compileEnv vyperTypeSystem vyperTypeExprResult vyperTyping vyperInterpreter
  vyperState finite_map
Libs
  monadsyntax

Theorem body_annassign_mem_rhs_pre[local]:
  !cenv cx env e es tops id typ ctx.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    body_stmt_safe tops (AnnAssign id typ e) /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
  irule stmt_expr_body_pre >>
  gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[]
QED

(* A supported copy into a type other than the source's, and not a word,
   is a bytestring copy. *)
Theorem copy_types_not_word_bytestring_mem[local]:
  !dst src.
    supported_copy_types dst src /\ dst <> src /\ ~is_word_type dst ==>
    is_bytestring_type dst
Proof
  simp[supported_copy_types_def] >> rpt strip_tac
  >- metis_tac[supported_word_type_is_word] >>
  BasicProvers.every_case_tac >> gvs[is_bytestring_type_def]
QED

Theorem body_annassign_mem_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) ==>
    body_stmt_mem_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_mem_ok_def] >>
  `supported_expr tops e /\ supported_copy_types typ (expr_type e)` by
    gvs[supported_stmt_def] >>
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
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_mem_rhs_pre] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  `!st0 c st1. declare_local cenv id typ st0 = (c, st1) ==>
     expr_sim_mem ctx func c cx (expr_type e) e es /\
     expr_vv_sim_mem ctx func c cx (expr_type e) e es` by
    (rpt gen_tac >> strip_tac >>
     `same_frame cenv c` by
       (drule_then irule declare_local_same_frame >> simp[]) >>
     `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
     `stmt_exprs_ok c (AnnAssign id typ e)` by
       metis_tac[stmt_exprs_ok_same_frame] >>
     `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
     `expr_body_pre c cx env e es` by metis_tac[body_annassign_mem_rhs_pre] >>
     metis_tac[body_expr_mem_ok_def]) >>
  Cases_on `is_word_type typ`
  >- suspend "word" >>
  `0 < type_memory_bytes cenv typ` by
    (irule expr_sim_inv_memory_bytes_pos >> metis_tac[]) >>
  `type_memory_bytes cenv typ = type_memory_size tyv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_size tyv + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- suspend "empty" >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
            is_bytestring_type (expr_type e) /\
            is_bytestring_type (lowered_value_type cenv e) /\
            arg_type_fits (lowered_value_type cenv e) (expr_type e)`
  >- (Cases_on `is_bytestring_type typ`
      >- suspend "bytes" >>
      suspend "copy") >>
  irule body_annassign_widened_aggregate_call_mem >> metis_tac[]
QED

Resume body_annassign_mem_case[word]:
  `expr_type e = typ` by metis_tac[type_widens_to_word] >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  irule compile_annassign_stmt_frag_mem >>
  simp[is_word_type_no_length_word, wordsTheory.dimword_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[] >>
      metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows]) >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
  `value_has_type tyv v` by
    gvs[expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, value_runtime_typed_def] >>
  irule store_lays_out_typed >> metis_tac[]
QED

Resume body_annassign_mem_case[empty]:
  irule compile_annassign_empty_stmt_frag_mem >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  metis_tac[memory_rhs_empty_eval_destination]
QED

Resume body_annassign_mem_case[copy]:
  `expr_type e = typ` by
    (CCONTR_TAC >> metis_tac[copy_types_not_word_bytestring_mem]) >>
  `lowered_value_type cenv e = typ` by gvs[] >>
  irule compile_annassign_copy_stmt_frag_mem >> simp[] >> rpt conj_tac
  >>~- ([`value_has_type _ _`],
    rpt gen_tac >> strip_tac >>
    `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
    `value_runtime_typed env typ v` by
      (irule memory_rhs_read_destination_typed >>
       qexistsl_tac [`cenv`, `cx`, `e`, `es with gas_obs := gs`, `es1`] >>
       rpt conj_tac
       >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC) >>
       simp[type_widens_to_def]) >>
    gvs[value_runtime_typed_def]) >>
  metis_tac[]
QED

Resume body_annassign_mem_case[bytes]:
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_to_def, arg_type_fits_bytestring_source] >>
  `is_bytestring_type (lowered_value_type cenv e)` by metis_tac[] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <=
     type_memory_bytes cenv typ` by
    (irule memory_rhs_destination_bound >> metis_tac[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by
    decide_tac >>
  drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
  drule expr_body_pre_type_evaluates >>
  disch_then (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME etv` >>
  `type_memory_size ltv <= type_memory_size tyv` by metis_tac[] >>
  `type_memory_bytes cenv (expr_type e) <= type_memory_bytes cenv typ` by
    metis_tac[type_widens_to_def, arg_type_fits_bytestring_memory_bytes,
              arithmeticTheory.LESS_EQ_REFL] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <=
     type_memory_bytes cenv (expr_type e)` by
    (irule lowered_value_type_memory_bound >> metis_tac[]) >>
  `type_memory_bytes cenv (expr_type e) < 2 ** 64` by decide_tac >>
  `type_memory_size ltv < dimword (:256)` by decide_tac >>
  irule compile_annassign_bytes_stmt_frag_mem >> simp[PULL_EXISTS] >>
  rpt conj_tac
  >>~- ([`value_has_type _ _`],
    rpt gen_tac >> strip_tac >>
    `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
    `value_runtime_typed env typ v /\
     value_runtime_typed env (expr_type e) v /\
     value_runtime_typed env (lowered_value_type cenv e) v` by
      metis_tac[memory_rhs_read_destination_typed,
                memory_rhs_read_lowered_typed, type_widens_to_def] >>
    gvs[value_runtime_typed_def])
  >>~- ([`gas_outcome _ _ _ _ _ _ _`],
    rpt gen_tac >> strip_tac >>
    `same_frame cenv c` by
      (drule_then irule declare_local_same_frame >> simp[]) >>
    `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
    `stmt_exprs_ok c (AnnAssign id typ e)` by
      metis_tac[stmt_exprs_ok_same_frame] >>
    `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
    `expr_body_pre c cx env e es` by metis_tac[body_annassign_mem_rhs_pre] >>
    drule_all declare_local_memory_types_mem >> strip_tac >>
    `type_memory_bytes c (expr_type e) = type_memory_size etv` by
      metis_tac[expr_sim_inv_memory_size] >>
    mp_tac (Q.SPECL [`tops`, `ctx`, `func`, `c`, `cx`, `env`, `e`, `es`, `ltv`,
                     `etv`] annassign_bytes_rhs_located_mem) >>
    impl_tac >- (rpt conj_tac >> gvs[] >> metis_tac[]) >>
    simp[]) >>
  metis_tac[]
QED

Finalise body_annassign_mem_case
