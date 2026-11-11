(*
 * The body simulation of S1: declaration cases (#637)
 *
 * The cases of body_sim_mutual that declare a local: AnnAssign, and For,
 * whose loop variable is one.  Every declaration lemma (stmtSimDecl,
 * stmtSimDeclMem, stmtSimDeclEmpty, stmtSimFor, stmtSimForRange) asks
 * that the declared name is unbound in the compile env or held through a
 * pointer.  The typing declares only a name not in env.var_types, and
 * ce_locals_declared (bodySim) binds no other local, so the name is
 * unbound (declared_name_unbound).  The loop's scope pop also rests on
 * bodySimStmtCases' eval_stmts_popped_keys_indexed.
 *
 * TOP-LEVEL:
 *   declared_name_unbound        — a declared name is unbound
 *   declare_local_same_frame, expr_sim_inv_declare_local — the compile
 *                                  env of a declaration is a frame where
 *                                  the statement's expressions simulate
 *   expr_sim_inv_for_scope, expr_sim_inv_for_pop — expr_sim_inv into
 *                                  and out of a loop iteration's scope
 *   body_annassign_case, body_for_case — the cases
 *   body_annassign_memory        — the declarations in memory
 *   body_annassign_other         — the declarations it leaves, which are
 *                                  unsupported
 *   body_for_other               — dispatcher for computed ranges and arrays
 *   body_for_array               — iteration over a fixed array
 *   body_for_range               — checked integer-range body simulation
 *)

Theory bodySimDeclCases
Ancestors
  supportedExprTraverse allocLimitsProps
  valueEncodingDefs exprSimSource
  bodyExprPreFacts
  stmtSimProps
  exprSimHypsDefs
  vyperTypeStoragePreservation
  list finite_map bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps stmtSimDecl stmtSimReturn stmtSimAssign bodyExprPreFacts bodyAppendStorageFacts
  stmtSimDeclMem stmtSimDeclEmpty memoryLocalRhsProps
  stmtSimFor stmtSimForParts stmtSimForRange stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag stmtSimForArrayFrame vyperTyping
  fragExec compileEnv supportedStmts supportedStmtTraverse vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeValues
  vyperTypeEvalSoundness vyperTypeEnvPreservation vyperTypeEnvExtension
  vyperTypeScopePop vyperEvalOutcomeSuffix vyperTypeCallGraph
  vyperEvalPreservesScopes
  vyperTypeCallStackSoundness compileVyper moduleLowering intCallCallee
Libs
  monadsyntax

(* ===== Declared names ===== *)

(* The typing declares only a name it does not know, which the compile env
   then does not bind. *)
Theorem declared_name_unbound:
  !cenv env ret_ty s env' id.
    ce_locals_declared cenv env /\ type_stmt env ret_ty s = SOME env' /\
    ((?typ e. s = AnnAssign id typ e) \/
     (?typ it n body. s = For id typ it n body)) ==>
    FLOOKUP cenv.ce_vars id = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  fs[ce_locals_declared_def] >> metis_tac[]
QED

(* ===== The compile env of a declaration ===== *)

Theorem declare_local_same_frame:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) ==>
    same_frame cenv c
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  rw[same_frame_def] >> Cases_on `n = id` >> gvs[]
QED

(* Declaring a name the typing does not know keeps expr_sim_inv: its
   clauses speak of the names in env.var_types only. *)
Theorem expr_sim_inv_declare_local:
  !cenv cx env es id ty st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx env es
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  `c.ce_var_type = (id =+ SOME ty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
          LET_THM] >> strip_tac >> gvs[]) >>
  `c.ce_flag_member_id = cenv.ce_flag_member_id /\
   c.ce_flag_n_members = cenv.ce_flag_n_members /\
   c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_hashmap_info = cenv.ce_hashmap_info /\
   c.ce_module_var_type = cenv.ce_module_var_type /\
   c.ce_module = cenv.ce_module /\
   c.ce_module_vars = cenv.ce_module_vars /\
   c.ce_is_ctor = cenv.ce_is_ctor /\
   c.ce_func_return_type = cenv.ce_func_return_type /\
   c.ce_method_id = cenv.ce_method_id` by
    (qpat_x_assum `_ with <| ce_vars := _; ce_var_type := _;
                             ce_dynarray_capacity := _ |> = cenv`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `place_map_tables_agree_on_defined c env <=>
   place_map_tables_agree_on_defined cenv env` by
    (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> simp[]) >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id` by
    (rpt strip_tac >> gvs[FLOOKUP_DEF]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==>
         ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
    metis_tac[] >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> c.ce_var_type n = SOME t` by
    (rw[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def]
QED

(* ===== AnnAssign ===== *)

Theorem body_annassign_rhs_pre[local]:
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
  `cx_tops cx = tops` by (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  irule stmt_expr_body_pre >>
  gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[]
QED

(* A declaration of a word type: stmtSimDecl's
   compile_annassign_typed_stmt_frag.  A word type takes no wider type, so
   the value has the declared type itself. *)
Theorem body_annassign_word[local]:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    body_stmt_safe tops (AnnAssign id typ e) /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    is_word_type typ ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env e /\ expr_type e = typ /\
   id NOTIN FDOM env.var_types` by
    (gvs[type_stmt_def, AllCaseEqs()] >> metis_tac[type_widens_to_word]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
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
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `body_expr_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  irule compile_annassign_typed_stmt_frag >>
  simp[is_word_type_no_length_word, wordsTheory.dimword_def] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
      drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, value_runtime_typed_def]) >>
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- metis_tac[compile_expr_grows] >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `expr_body_pre c cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  metis_tac[body_expr_ok_def]
QED

Theorem body_annassign_declared_rhs[local]:
  !cenv cx env e es tops id typ st c st1 ctx func.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    body_stmt_safe tops (AnnAssign id typ e) /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    body_expr_ok cx e /\ declare_local cenv id typ st = (c,st1) ==>
    expr_sim ctx func c cx (expr_type e) e es /\
    expr_vv_sim ctx func c cx (expr_type e) e es
Proof
  rpt strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `expr_body_pre c cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  metis_tac[body_expr_ok_def]
QED

(* A declaration of a type that is not a word, from a value of the type
   itself, a bytestring (a narrower one widens), or an empty value of a
   type with a length word: stmtSimDeclMem's
   compile_annassign_memory_widen_stmt_frag and stmtSimDeclEmpty's
   compile_annassign_empty_stmt_frag.  The declared type is below 2 ** 64
   (alloc_limits_stmt), so its buffer and a bytestring copy's length word
   fit below 2 ** 256. *)
Theorem body_annassign_memory:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    body_stmt_safe tops (AnnAssign id typ e) /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
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
  `body_expr_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `type_memory_bytes cenv typ = type_memory_size tyv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_size tyv + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- suspend "empty" >>
  suspend "copy"
QED

Resume body_annassign_memory[copy]:
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
  irule compile_annassign_memory_widen_stmt_frag >>
  gns[] >> rpt conj_tac
  >>~- ([`expr_sim _ _ _ _ _ _ _`],
    rpt gen_tac >> strip_tac >>
    metis_tac[body_annassign_declared_rhs, exprLoweringPropsTheory.compile_expr_grows])
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

Resume body_annassign_memory[empty]:
  irule compile_annassign_empty_stmt_frag >> gns[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      metis_tac[body_annassign_declared_rhs, exprLoweringPropsTheory.compile_expr_grows]) >>
  rpt gen_tac >> strip_tac >>
  metis_tac[memory_rhs_empty_eval_destination]
QED

Finalise body_annassign_memory

(* A declared type takes memory: it is assignable, so it takes a storage slot
   (assignable_type_slot_size_pos). *)
Theorem annassign_memory_bytes_pos[local]:
  !cenv cx env es ret_ty id typ e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' ==>
    0 < type_memory_bytes cenv typ
Proof
  rpt strip_tac >>
  `assignable_type env.type_defs typ` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

(* A supported copy into a type other than the source's, and not a word,
   is a bytestring copy. *)
Theorem copy_types_not_word_bytestring[local]:
  !dst src.
    supported_copy_types dst src /\ dst <> src /\ ~is_word_type dst ==>
    is_bytestring_type dst
Proof
  simp[supportedTypesTheory.supported_copy_types_def] >> rpt strip_tac
  >- metis_tac[typedCopyMetadataTheory.supported_word_type_is_word] >>
  BasicProvers.every_case_tac >> gvs[is_bytestring_type_def]
QED

(* The declarations body_annassign_memory leaves are not supported: a
   supported declaration copies a value of the declared type itself, a
   word, or a bytestring (supported_copy_types). *)
Theorem body_annassign_other:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    ~(expr_type e = typ \/ is_bytestring_type typ \/
      has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt strip_tac >>
  `supported_copy_types typ (expr_type e)` by
    (qpat_x_assum `supported_stmt _ _ _` mp_tac >> simp[supported_stmt_def]) >>
  metis_tac[copy_types_not_word_bytestring]
QED

(* RESIDUAL (#767): a memory-backed declaration of an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise). *)
Theorem body_annassign_widened_aggregate_call:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

Theorem body_annassign_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) ==>
    body_stmt_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `is_word_type typ`
  >- (irule body_annassign_word >> metis_tac[]) >>
  `0 < type_memory_bytes cenv typ` by
    metis_tac[annassign_memory_bytes_pos] >>
  Cases_on `expr_type e = typ \/ lowered_value_type cenv e = typ \/
            is_bytestring_type typ \/
            has_length_word typ /\ is_empty_value_expr e`
  >- (Cases_on `(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e))`
      >- (`lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
           has_length_word typ /\ is_empty_value_expr e` by metis_tac[] >>
          match_mp_tac (Q.SPECL
            [`cx`, `id`, `typ`, `e`, `tops`, `bindings`, `ctx`, `func`,
             `cenv`, `env`, `env'`, `ret_ty`, `lctx`, `RetQ`, `es`]
            body_annassign_memory) >>
          simp[] >> first_assum ACCEPT_TAC) >>
      irule body_annassign_widened_aggregate_call >> metis_tac[]) >>
  irule body_annassign_other >> metis_tac[]
QED

(* ===== For ===== *)

(* The scope of a loop's iteration: the loop variable, declared in the
   compile env and added to the type environment. *)
Theorem for_pushed_state_well_typed:
  !st tyv v id.
    state_well_typed st /\ value_has_type tyv v /\
    well_formed_type_value tyv ==>
    state_well_typed
      (st with scopes updated_by
         CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                popped := []|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem for_pushed_popped_keys[local]:
  !scs id tyv v.
    popped_keys_indexed scs ==>
    popped_keys_indexed
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                        popped := []|>) :: scs)
Proof
  rw[popped_keys_indexed_def, FLOOKUP_UPDATE] >> gvs[]
QED

Theorem scopes_CONS_updated:
  !es x. es with scopes := x :: es.scopes = es with scopes updated_by CONS x
Proof
  simp[evaluation_state_component_equality]
QED

Theorem expr_sim_inv_for_scope:
  !cenv cx env es id fty tyv v st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    declare_local cenv id fty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx (extend_local env id fty F)
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes)
Proof
  rpt strip_tac >> REWRITE_TAC [scopes_CONS_updated] >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `popped_keys_indexed
     (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                       popped := []|>) :: es.scopes)` by
    simp[for_pushed_popped_keys] >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_var_type = (id =+ SOME fty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
          LET_THM] >> strip_tac >> gvs[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >>
     metis_tac[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          c.ce_var_type n = SOME ty` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
          combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum
    `_ with <| ce_vars := _; ce_var_type := _;
               ce_dynarray_capacity := _ |> = cenv`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `(place_map_tables_agree_on_defined c (extend_local env id fty F) <=>
    place_map_tables_agree_on_defined cenv env) /\
   (extend_local env id fty F).bare_globals = env.bare_globals` by
    (conj_tac >- (irule placeTypingPropsTheory.place_map_tables_agree_on_defined_cong >> fs[extend_local_def]) >>
     simp[extend_local_def]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[] >>
  conj_tac >- fs[extend_local_def] >>
  irule storage_conjs_scopes >> simp[]
QED

(* After an iteration that goes on (a normal end or a continue), with the
   loop variable's scope popped, expr_sim_inv holds again at the loop's
   compile and type environments: the type soundness of the body, and
   vyperTypeEvalSoundness's for_body_env_consistent_after_pop. *)
Theorem expr_sim_inv_for_pop:
  !cenv cx env es id fty tyv v ret_ty body env_b r2 es2 sc rest tops
   bindings.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_stmts cx body
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes) = (r2, es2) /\
    (r2 = INL () \/ r2 = INR ContinueException) /\
    es2.scopes = sc :: rest /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings body ==>
    expr_sim_inv cenv cx env (es2 with scopes := rest)
Proof
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  RULE_ASSUM_TAC (REWRITE_RULE [scopes_CONS_updated]) >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `accounts_well_typed
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>))).accounts` by simp[] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >>
  `env_maps_wf env` by metis_tac[env_consistent_env_maps_wf] >>
  `env_consistent env cx (es2 with scopes := TL es2.scopes)` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     qpat_x_assum `sum_CASE _ _ _` mp_tac >> simp_tac (srw_ss()) [] >>
     strip_tac
     >- (irule for_body_env_consistent_after_pop >> metis_tac[]) >>
     irule for_body_env_extends_consistent_after_pop >> metis_tac[]) >>
  `state_well_typed (es2 with scopes := TL es2.scopes)` by
    (irule scope_bracket_preserves_swt >> metis_tac[]) >>
  `outcomes_accounts_typed es2.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 2 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  `popped_keys_indexed es2.scopes` by
    (`runtime_consistent (extend_local env id fty F) cx
        (es with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                 popped := []|>)))` by
       simp[runtime_consistent_def] >>
     `popped_keys_indexed
        (es with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                 popped := []|>))).scopes` by
       simp[for_pushed_popped_keys] >>
     drule_all (cj 2 eval_stmts_popped_keys_indexed) >> simp[]) >>
  `popped_keys_indexed rest` by gvs[popped_keys_indexed_def] >>
  `contract_storage_well_formed cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>))) /\
   oracle_storage_ok cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule storage_conjs_scopes >> simp[]) >>
  `runtime_storage_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>))) /\
   IS_SOME (es with scopes updated_by
              CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                     popped := []|>))).outcomes` by
    simp[runtime_storage_consistent_def, runtime_consistent_def] >>
  drule_all (cj 2 eval_stmts_storage_conjs) >> strip_tac >>
  `contract_storage_well_formed cx (es2 with scopes := rest) /\
   oracle_storage_ok cx (es2 with scopes := rest)` by
    (irule storage_conjs_scopes >> simp[]) >>
  qpat_x_assum `es2.scopes = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (REWRITE_RULE [TL]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

Theorem compile_stmts_grows[local]:
  !c lc ty stmts sa sb.
    compile_stmts c lc ty stmts sa = ((), sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
  simp[]
QED

Theorem is_int_type_word[local]:
  !t. is_int_type t ==> is_word_type t
Proof
  Cases >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def]
QED

(* A range of literals: stmtSimFor's compile_for_range_lit_frag, whose
   invariant is expr_sim_inv at the loop's environments.  The literals'
   type bounds the rounds below 2 ** 256. *)
Theorem eval_stmts_gas_obs_scopes[local]:
  !cx stmts ei gs sc r es2.
    eval_stmts cx stmts (ei with <| scopes := sc :: ei.scopes; gas_obs := gs |>) =
      (r, es2) ==>
    eval_stmts cx stmts
      ((ei with gas_obs := gs) with scopes := sc :: (ei with gas_obs := gs).scopes) =
      (r, es2)
Proof
  simp[]
QED

(* A loop's body has the abi-decode targets of the loop. *)
Theorem for_body_abi_targets[local]:
  !tops id typ it n body.
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) ==>
    !target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops
Proof
  simp[supported_stmt_expr_exists_def]
QED

Theorem body_for_range_lit[local]:
  !cx id typ a1 n1 a2 n2 n stmts tops bindings ctx func cenv env env'
   ret_ty lctx RetQ es res es'.
    body_stmt_safe tops
      (For id typ
        (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n stmts) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\
       eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id stmts vs) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) = SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts))
      (eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n stmts)) es
Proof
  rpt strip_tac >>
  imp_res_tac body_stmt_safe_for_body >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_literal typ (IntL n1) /\ well_typed_literal typ (IntL n2) /\
   well_formed_type env.type_defs typ /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `n1 <= n2 /\ n = Num (n2 - n1) /\ supported_stmts tops bindings stmts` by
    gvs[supported_stmt_def, supported_iterator_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `!k. well_typed_literal typ (IntL k) ==> value_has_type tyv (IntV k)` by
    (rpt strip_tac >> drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)) <> [] ==>
   body_stmts_ok cx stmts` by
    (strip_tac >>
     first_x_assum (qspecl_then [`get_tenv cx`, `es`, `tyv`, `es`, `es`,
       `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))`, `es`, `es`, `()`,
       `es`] mp_tac) >>
     simp[lift_option_type_def, return_def, eval_iterator_range_lit,
          check_def, assert_def, compatible_bound_def, body_for_ok_def]) >>
  `Num (n2 - n1) < dimword (:256)` by metis_tac[range_end_words] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  drule_all is_int_type_word >> strip_tac >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  MATCH_MP_TAC
    (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei`
                  compile_for_range_lit_frag)) >>
  qexists_tac `tyv` >> simp[wordsTheory.dimword_def] >> rpt conj_tac
  >- metis_tac[compile_stmts_grows]
  >- (rpt strip_tac >>
      `body_stmts_ok cx stmts` by
        (first_x_assum irule >> simp[listTheory.GENLIST_EQ_NIL] >>
         strip_tac >> gvs[]) >>
      `same_frame cenv c` by
        (drule_then irule declare_local_same_frame >> simp[]) >>
      `value_has_type tyv (IntV (n1 + &j))` by
        (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
      `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
      drule for_body_abi_targets >> strip_tac >>
      qpat_x_assum `body_stmts_ok _ _`
        (irule o REWRITE_RULE [body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff]) >>
      simp[] >> rpt conj_tac
      >- fs[body_stmts_safe_iff]
      >- fs[body_stmts_safe_iff]
      >- metis_tac[stmt_exprs_ok_same_frame]
      >- (qexistsl_tac [`bindings`, `tops`] >> simp[] >>
          fs[body_stmts_safe_iff])
      >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
          `c.ce_struct_fields = cenv.ce_struct_fields` by
            metis_tac[same_frame_struct_fields] >>
          metis_tac[expr_sim_inv_for_scope, ce_locals_declared_declare_local,
                    locals_alloc_ok_extend]) >>
      metis_tac[frame_ret_ok_same_frame]) >>
  rpt strip_tac >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  drule eval_stmts_gas_obs_scopes >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def] >>
  drule_at (Pat `eval_stmts`) expr_sim_inv_for_pop >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexistsl_tac [`env_b`, `typ`, `ret_ty`] >> simp[]) >>
  metis_tac[]
QED

(* The source checker validates computed bounds in the loop's integer type. *)
Theorem body_range_typing:
  !(env, ret_ty, id, typ, e1, e2, bound, stmts) env'.
    type_stmt env ret_ty (For id typ (Range e1 e2) bound stmts) = SOME env' /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\
                       e2 = Literal a2 (IntL n2)) ==>
    id NOTIN FDOM env.var_types /\ is_int_type typ /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    expr_type e1 = typ /\ expr_type e2 = typ /\
    well_formed_type env.type_defs typ /\
    0 < bound /\ well_typed_literal typ (IntL (&bound)) /\
    ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b
Proof
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`env`, `ret_ty`, `id`, `typ`, `e1`, `e2`, `bound`, `stmts`] >>
  rpt gen_tac >> strip_tac >>
  `((case Range e1 e2 of
       Range (Literal _ (IntL _)) (Literal _ (IntL _)) => T
     | Range _ _ => 0 < bound /\ well_typed_literal typ (IntL (&bound))
     | Array _ => T) =
    (0 < bound /\ well_typed_literal typ (IntL (&bound))))` by
    (Cases_on `e1` >> gvs[] >>
     rename1 `Literal a lit` >> Cases_on `lit` >> gvs[] >>
     Cases_on `e2` >> gvs[] >>
     rename1 `Range _ (Literal a' lit')` >> Cases_on `lit'` >> gvs[]) >>
  gvs[type_stmt_def, well_typed_iterator_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[assignable_type_well_formed]
QED

(* A successful typed integer endpoint preserves the loop invariant. *)
Theorem body_range_endpoint_read:
  !(cenv, cx, env, e, typ, tyv) es tv es'.
    expr_body_pre cenv cx env e es /\ is_int_type typ /\
    expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
    (do raw <- eval_expr cx e; read_result cx raw od) es = (INL tv, es') ==>
    expr_sim_inv cenv cx env es' /\
    ?n. tv = IntV n /\ value_has_type tyv (IntV n)
Proof
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`cenv`, `cx`, `env`, `e`, `typ`, `tyv`] >>
  rpt gen_tac >> strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      expr_runtime_typed_def, value_result_typed_def] >>
  Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >> gvs[is_int_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `tv` >> gvs[vyperTypingTheory.value_has_type_def]
QED

(* A successful nonempty checked iterator activates the source body IH. *)
Theorem body_for_range_active[local]:
  !(cx, id, typ, e1, e2, bound, body, tyv) lo hi es0 es1 es2.
    (!tenv s'' tv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tv,t) /\
       eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==> body_for_ok cx tv id body vs) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    (do raw <- eval_expr cx e1; read_result cx raw od) es0 = (INL (IntV lo), es1) /\
    (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (INL (IntV hi), es2) /\
    lo <= hi /\ Num (hi - lo) <= bound /\ 0 < Num (hi - lo) ==>
    body_stmts_ok cx body
Proof
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`cx`, `id`, `typ`, `e1`, `e2`, `bound`, `stmts`, `tyv`] >>
  rpt gen_tac >> strip_tac >>
  `eval_iterator cx (Range e1 e2) es0 =
   (INL (GENLIST (\j. IntV (lo + &j)) (Num (hi - lo))), es2)` by
    (gvs[bind_def, AllCaseEqs()] >>
     simp[Once evaluate_def, bind_def, get_range_limits_def,
          lift_sum_def, return_def]) >>
  gvs[lift_option_type_def, return_def, check_def, assert_def,
      compatible_bound_def] >>
  first_x_assum drule >>
  simp[body_for_ok_def, GENLIST_EQ_NIL] >>
  Cases_on `hi = lo` >> gvs[]
QED

(* The enclosing For carries both traversal and allocation safety for its body. *)
Theorem body_for_exprs_ok:
  !cenv id typ it n body.
    stmt_exprs_ok cenv (For id typ it n body) ==>
    EVERY (stmt_exprs_ok cenv) body
Proof
  simp[stmts_exprs_ok_EVERY, stmt_exprs_ok_def,
       supported_stmt_expr_exists_def, alloc_limits_stmt_def,
       stmt_valued_return_def]
QED

(* Normalize only a paired outer binder at theorem application boundaries. *)
fun range_tuple_forall th =
  SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) th);

(* Integer ranges use checked endpoints unless the frontend supplies two
   source integer literals. Array iteration remains a separate residual.
   body_for_ok supplies a body judgment only for a successfully checked,
   nonempty iterator; rejecting and empty ranges need no body judgment. *)
Theorem body_for_range:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    (?e1 e2. it = Range e1 e2) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> gvs[] >>
  Cases_on `?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)`
  >- (gvs[] >> irule body_for_range_lit >> simp[] >> metis_tac[]) >>
  drule (range_tuple_forall body_range_typing) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `body_iterator_ok cx (Range e1 e2)` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def] >> metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  drule_all is_int_type_word >> strip_tac >>
  drule_all word_type_sizes >> strip_tac >>
  `value_has_type tyv (IntV (&n))` by
    (drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `value_has_type tyv (IntV 0)` by
    (Cases_on `typ` >> gvs[is_int_type_def] >>
     rename1 `evaluate_type _ (BaseT bt) = _` >> Cases_on `bt` >>
     gvs[is_int_type_def, vyperValueTheory.evaluate_type_def,
         vyperTypingTheory.value_has_type_def, vyperValueTheory.within_int_bound_def]) >>
  `n < dimword (:256)` by
    (drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
     disch_then (qspecl_then [`0`, `&n`] mp_tac) >> simp[]) >>
  `supported_pure_expr tops e1 /\ supported_pure_expr tops e2` by
    (qpat_x_assum `supported_stmt _ _ _` mp_tac >>
     simp[supported_stmt_def, supported_iterator_def] >>
     Cases_on `e1` >> gvs[] >>
     rename1 `Range (Literal a lit) _` >> Cases_on `lit` >> gvs[] >>
     Cases_on `e2` >> gvs[] >>
     rename1 `Range _ (Literal a' lit')` >> Cases_on `lit'` >> gvs[]) >>
  `supported_expr tops e1 /\ supported_expr tops e2` by
    simp[supportedExprsTheory.supported_expr_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by (irule gasContextTheory.cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    fs[body_inv_def] >>
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
  `expr_body_pre cenv cx env e1 es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_expr e2 ++ int_calls_stmts body'` >> simp[]) >>
  `!ei. expr_sim_inv cenv cx env ei ==> expr_body_pre cenv cx env e2 ei` by
    (rpt strip_tac >> irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_iterator_exists_def, int_calls_stmt_def, int_calls_iterator_def] >>
     qexists_tac `int_calls_stmts body'` >>
     metis_tac[call_evaluation_safe_append_right, listTheory.APPEND_ASSOC]) >>
  `expr_sim ctx func cenv cx typ e1 es` by
    (gvs[body_iterator_ok_def, body_expr_ok_def] >> metis_tac[]) >>
  `!x t. FLOOKUP env.var_types x = SOME t ==> well_formed_type env.type_defs t` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     simp[NoAsms, expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     rpt strip_tac >> simp[well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  MATCH_MP_TAC (range_tuple_forall
    (Q.SPECL [`expr_sim_inv cenv cx env`, `body_stmts_ok cx body'`]
       compile_for_range_checked_frag_active)) >>
  qexistsl_tac [`env`, `tyv`] >> simp[wordsTheory.dimword_def] >>
  rpt conj_tac
  >- metis_tac[compile_stmts_grows]
  >- suspend "endpoints"
  >- suspend "active"
  >- metis_tac[]
  >- metis_tac[]
  >- suspend "body"
  >> suspend "pop"
QED

Resume body_for_range[endpoints]:
  rpt strip_tac >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 es` kall_tac >>
  drule (range_tuple_forall body_range_endpoint_read) >>
  disch_then (qspec_then `tyv` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `tv = IntV lo` >> qexists_tac `lo` >> simp[] >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  conj_tac
  >- (gvs[body_iterator_ok_def, body_expr_ok_def, bind_def, AllCaseEqs()] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e2 (es1 with gas_obs := gs2)` by simp[] >>
  qpat_x_assum `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` kall_tac >>
  qpat_x_assum `expr_body_pre cenv cx env e2 es1` kall_tac >>
  drule (range_tuple_forall body_range_endpoint_read) >>
  disch_then (qspec_then `tyv` mp_tac) >> simp[]
QED

Resume body_for_range[active]:
  rpt strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (range_tuple_forall body_for_range_active)) >> simp[]
QED

Resume body_for_range[body]:
  rpt strip_tac >>
  drule supported_loop_body_contract >> strip_tac >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) body'` by
    metis_tac[body_for_exprs_ok] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  drule for_body_abi_targets >> strip_tac >>
  qpat_x_assum `body_stmts_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[] >>
          fs[body_stmts_safe_iff])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      conj_tac
      >- (irule ce_locals_declared_declare_local >> metis_tac[]) >>
      conj_tac
      >- (irule locals_alloc_ok_extend >> qexists_tac `cenv` >>
          simp[] >> metis_tac[same_frame_struct_fields]) >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_same_frame]
QED

Resume body_for_range[pop]:
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule supported_loop_body_contract >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (fs[int_calls_stmt_def, int_calls_iterator_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  drule eval_stmts_gas_obs_scopes >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs)` by simp[] >>
  drule_at (Pat `eval_stmts`) expr_sim_inv_for_pop >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexistsl_tac [`env_b`, `typ`, `ret_ty`] >> simp[]) >>
  metis_tac[]
QED

Finalise body_for_range

(* A loop over an array (#637 for, #559): the iterable is a variable
   holding a fixed array of the loop variable's type (supported_iterator),
   which the body does not write (type_stmt's iterator_unmodified).  The
   lowering reads each element from the array's place at each iteration,
   the source iterates over the array's value read once before the loop;
   the two agree as the body leaves the array's value unchanged.
   Why it holds: a source Name is a memory place, and expr_sim_inv binds it
   to a PtrVar whose bytes hold the value (val_in_memory); the body has no
   internal calls and iterator_unmodified (via stmt_writes_ok) rejects
   every statement that could write it, so the variable's value, and with
   the state relation the bytes the lowering reads, are those of the
   snapshot at every iteration.  The element at index j of a fixed array
   lies at j * type_memory_bytes of the element (val_in_memory_sarray,
   elems_in_memory_EL); the element and loop types are equal, so the copy
   is MLOAD/MSTORE for a word and compile_store_memory at one type
   otherwise (compile_store_memory_run).  m < 2 ** 256, since evaluate_type
   bounds the array's size. *)
Theorem array_for_source_ready[local]:
  (!tenv s tyv t s3 vs t3 s4 x t4.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tyv,t) /\
    eval_iterator cx (Array e) s3 = (INL vs,t3) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t4)
    ==> body_for_ok cx tyv id stmts vs) /\
  supported_stmt tops bindings (For id typ (Array e) n stmts) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n stmts) = SOME env' ==>
  ?name env_b entry tv ptr sz al vs.
    e = Name (ArrayT typ (Fixed n)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT typ (Fixed n)) name) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ (Fixed n)) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    entry.type = ArrayTV tv (Fixed n) /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    cenv.ce_var_type name = SOME (ArrayT typ (Fixed n)) /\
    0 < n /\ n < dimword (:256) /\ entry.value = ArrayV (SArrayV al) /\
    vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV al) /\ LENGTH vs = n /\
    (!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
            (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
    body_stmts_ok cx stmts /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule_all array_for_hypotheses >> strip_tac >> gvs[] >>
  drule_all array_name_local_binding >> strip_tac >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `?al. entry.value = ArrayV (SArrayV al)` by
    (Cases_on `entry.value` >> gvs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
     gvs[value_has_type_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Fixed n)) =
     SOME (ArrayTV tv (Fixed n))` by
    (fs[expr_sim_inv_def, well_typed_expr_def, env_consistent_def,
        env_scopes_consistent_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
          (es with gas_obs := gs) =
        (INL (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)),
         es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_fixed_name >> simp[]) >>
  drule_all eval_iterator_fixed_name >> strip_tac >>
  qmatch_asmsub_abbrev_tac `INL vs` >>
  `LENGTH vs = n` by simp[Abbr `vs`, fixed_array_elements_length] >>
  `body_for_ok cx tv id stmts vs` by
    (qpat_x_assum `!s tyv t s3 vs t3 s4 t4. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[]) >>
  `body_stmts_ok cx stmts` by
    (fs[body_for_ok_def] >> `vs <> []` by (strip_tac >> gvs[]) >> metis_tac[]) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  qexistsl_tac [`entry`, `tv`] >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `al` >> fs[Abbr `vs`]
QED

Theorem array_for_layout_ready:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  stmt_exprs_ok cenv (For id typ (Array e) n stmts) ==>
  type_memory_bytes cenv typ = type_memory_size tv /\
  type_memory_bytes cenv typ + 64 < dimword (:256)
Proof
  strip_tac >> conj_tac >- metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  fs[wordsTheory.dimword_def] >> decide_tac
QED

Theorem array_body_fragment_callback:
  !cx stmts tops ctx cenv bindings env ei id typ tv v env_b ret_ty
   func RetQ st0 bc sd ex inc.
    body_stmts_safe tops stmts /\
    body_stmts_ok cx stmts /\ body_inv tops ctx cenv cx /\
    supported_stmts tops bindings stmts /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) stmts ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env ei /\
    ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    EVERY (stmt_exprs_ok cenv) stmts /\
    type_memory_bytes cenv typ < 2 ** 64 /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    declare_local cenv id typ st0 = (bc,sd) ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ret_ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[ce_locals_declared_def] >>
     metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv bc` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx bc cx` by metis_tac[body_inv_same_frame] >>
  qpat_x_assum `body_stmts_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff]) >>
  simp[] >> rpt conj_tac
  >- fs[body_stmts_safe_iff]
  >- fs[body_stmts_safe_iff]
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[] >>
          fs[body_stmts_safe_iff])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `bc.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      conj_tac >- metis_tac[locals_alloc_ok_extend] >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  metis_tac[frame_ret_ok_same_frame]
QED

Theorem array_body_scope_shape:
  !cx stmts ei id tv v r ef.
    lookup_scopes id ei.scopes = NONE /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    ?sc rest. ef.scopes = sc::rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE)
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
  Cases_on `ef.scopes` >- gvs[] >>
  rename1 `ef.scopes = sc::rest` >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> rpt strip_tac >>
  Cases_on `x = id` >- metis_tac[eval_stmts_preserves_tail_lookup_none] >>
  drule eval_stmts_new_in_head_not_in_tail >>
  disch_then (qspec_then `x` mp_tac) >> simp[]
QED

Theorem array_body_result_ok:
  !cx stmts cenv env ei id typ tv v ret_ty env_b r ef.
    expr_sim_inv cenv cx env ei /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    !ex inc. stmt_res_ok (InLoop ex inc) r
Proof
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (REWRITE_RULE [scopes_CONS_updated]) >>
  `env_consistent (extend_local env id typ F) cx
     (ei with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                              popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `accounts_well_typed
     (ei with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                              popped := []|>))).accounts` by simp[] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >>
  Cases_on `r` >> simp[stmtSimDefsTheory.stmt_res_ok_def] >>
  rename1 `no_type_error_result (INR err)` >>
  Cases_on `err` >> gvs[stmtSimDefsTheory.stmt_res_ok_def, no_type_error_result_def] >>
  rename1 `Error er` >> Cases_on `er` >>
  gvs[stmtSimDefsTheory.stmt_res_ok_def, no_type_error_result_def]
QED

Theorem array_body_direct_snapshot:
  !tops bindings stmts env id typ name elem bound ret_ty env_b aty
   cx ei tv v r ef sc rest entry.
    supported_stmts tops bindings stmts /\
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    iterator_unmodified (Array (Name aty name)) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name ei.scopes = SOME entry /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) /\
    ef.scopes = sc::rest ==>
    lookup_scopes name rest = SOME entry
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP (extend_local env id typ F).var_types name =
     SOME (ArrayT elem bound)` by simp[extend_local_def, FLOOKUP_UPDATE] >>
  `stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts` by
    gvs[iterator_unmodified_def, expr_place_def] >>
  drule_at (Pat `eval_stmts`) typed_stmts_projection_frame >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `MAP (\s. FLOOKUP s name) rest = MAP (\s. FLOOKUP s name) ei.scopes` by
    gvs[] >>
  drule scope_projection_lookup >> simp[]
QED

Theorem array_body_scope_callback:
  !cenv cx env ei id typ tv v ret_ty stmts env_b r ef tops bindings
   name elem bound aty entry.
    expr_sim_inv cenv cx env ei /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts stmts) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings stmts /\
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
    iterator_unmodified (Array (Name aty name)) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name ei.scopes = SOME entry /\
    lookup_scopes id ei.scopes = NONE /\
    eval_stmts cx stmts
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v;
                          popped := []|>)) :: ei.scopes) = (r,ef) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. ef.scopes = sc::rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        expr_sim_inv cenv cx env (ef with scopes := rest) /\
        lookup_scopes name rest = SOME entry /\ lookup_scopes id rest = NONE)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule array_body_result_ok >> metis_tac[]) >>
  drule_all array_body_scope_shape >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> disch_tac >>
  conj_tac >- (irule expr_sim_inv_for_pop >> metis_tac[]) >>
  conj_tac >- (irule array_body_direct_snapshot >> metis_tac[]) >>
  metis_tac[eval_stmts_preserves_tail_lookup_none]
QED

Theorem body_for_array:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    (?e. it = Array e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> qpat_x_assum `it = Array _` SUBST_ALL_TAC >>
  drule_all array_for_source_ready >> strip_tac >> gvs[] >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  rename1 `body_stmts_ok cx stmts` >>
  drule for_body_abi_targets >> strip_tac >>
  drule_all array_for_layout_ready >> strip_tac >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `FLOOKUP env.var_types name = SOME (ArrayT typ (Fixed n))` by
    fs[well_typed_expr_def, expr_type_def] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `EVERY (stmt_exprs_ok cenv) stmts /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az)` >>
  MATCH_MP_TAC
    (Q.GENL [`arr_ptr`, `arr_sz`, `tv`, `vs`]
      (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei /\
                              lookup_scopes name ei.scopes = SOME entry`
                   (Q.GEN `P` (SPEC_ALL compile_for_array_frag))))) >>
  qexistsl_tac [`ap`, `az`, `tv`,
    `array_elements (ArrayTV tv (Fixed n)) (SArrayV al)`] >>
  simp[] >> rpt conj_tac
  >- metis_tac[compile_stmts_grows]
  >- (rpt strip_tac >> metis_tac[fixed_array_elements_typed])
  >- (rpt strip_tac >> irule array_snapshot_memory >> metis_tac[])
  >- (rpt strip_tac >> irule array_body_fragment_callback >>
      metis_tac[fixed_array_elements_typed]) >>
  rpt gen_tac >> strip_tac >>
  drule_all fixed_array_elements_typed >> strip_tac >>
  drule eval_stmts_gas_obs_scopes >> strip_tac >>
  `expr_sim_inv cenv cx env (ei with gas_obs := gs) /\
   lookup_scopes name (ei with gas_obs := gs).scopes = SOME entry /\
   lookup_scopes id (ei with gas_obs := gs).scopes = NONE` by simp[] >>
  drule_at (Pat `eval_stmts`) array_body_scope_callback >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

Theorem body_for_other:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    body_stmt_safe tops (For id typ it n body) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt strip_tac >>
  imp_res_tac body_stmt_safe_for_body >> Cases_on `it`
  >- (irule body_for_array >> simp[] >> metis_tac[]) >>
  irule body_for_range >> simp[] >> metis_tac[]
QED

Theorem body_for_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) ==>
    body_stmt_ok cx (For id typ it n body)
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [body_stmt_ok_def] >>
  rpt strip_tac >>
  Cases_on `?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`
  >- (qpat_x_assum `?a1 n1 a2 n2. _`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) >>
      drule_all body_for_range_lit >> simp[]) >>
  drule_all body_for_other >> simp[]
QED
