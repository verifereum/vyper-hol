(*
 * The body simulation of S1: the Log case (#637)
 *
 * A supported log statement names an event of the main module whose fields
 * are word types or bytestrings, with arguments of the fields' types
 * (supported_log).  body_log_case gives it stmtSimLog's
 * compile_log_stmt_frag, with the argument judgments of the induction
 * hypothesis; the event's buffers fit below 2 ** 64, as the lowering's
 * alloc_limits_stmt checks.
 *
 * TOP-LEVEL:
 *   body_log_metadata    — the compile env and the source give a supported
 *                          event the same metadata
 *   body_log_args_ready  — the arguments' judgments, from the induction
 *                          hypothesis
 *   body_log_case        — the case of the induction
 *)

Theory bodySimLog
Ancestors
  allocLimits allocLimitsProps
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim bodySimStmtCases stmtSimLog exprSimHyps
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness

(* ===== The event's metadata ===== *)

Theorem supported_event_fields_some[local]:
  !tops id fields.
    supported_event_fields tops id = SOME fields ==>
    ?name. id = (NONE, name) /\ MEM (EventDecl name fields) tops /\
           !tenv. lookup_event_metadata_in tenv name tops =
                  SOME (event_hash tenv name (MAP (SND o FST) fields),
                        MAP (SND o FST) fields, MAP SND fields)
Proof
  Induct >> simp[supported_event_fields_def] >>
  rpt gen_tac >> PairCases_on `id` >>
  simp[supported_event_fields_def] >>
  Cases_on `id0` >> simp[] >> strip_tac >>
  Cases_on `h` >> fs[lookup_event_metadata_in_def, AllCaseEqs()] >>
  rw[] >> res_tac >> fs[]
QED

Theorem event_decl_names_mem[local]:
  !tops n a. MEM (EventDecl n a) tops ==> MEM n (supported_event_names tops)
Proof
  Induct >> simp[supported_event_names_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `h` >> simp[] >> metis_tac[]
QED

Theorem event_names_unique[local]:
  !tops n. ALL_DISTINCT (supported_event_names tops) ==> event_decl_unique n tops
Proof
  Induct >> simp[event_decl_unique_def, supported_event_names_def] >>
  Cases >> simp[] >> fs[event_decl_unique_def] >>
  metis_tac[event_decl_names_mem]
QED

(* A scalar type's ABI type does not look at the type environment. *)
Theorem scalar_abi_types_env[local]:
  !ts env env'.
    EVERY supported_scalar_type ts ==>
    vyper_to_abi_types env ts = vyper_to_abi_types env' ts
Proof
  Induct >> simp[] >> Cases >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

(* body_inv's ce_event_info is build_event_info's for the program, whose
   event names supported_program makes distinct, and the source finds the
   same declaration in the module get_module_code gives. *)
Theorem body_log_metadata:
  !tops ctx cenv cx id fields.
    body_inv tops ctx cenv cx /\ supported_event_fields tops id = SOME fields ==>
    ?h. cenv.ce_event_info (nsid_to_string id) =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
          SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3 /\
        EVERY supported_scalar_type (MAP (SND o FST) fields)
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_event_fields_some >> strip_tac >> gvs[] >>
  `EVERY supported_scalar_type (MAP (SND o FST) fields) /\
   LENGTH (FILTER I (MAP SND fields)) <= 3` by
    (gvs[body_inv_def, supported_program_def,
         supported_declaration_headers_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e tops ==> supported_declaration_header _ _`
       drule >>
     simp[supported_declaration_header_def, EVERY_MAP, combinTheory.o_DEF,
          MEM_MAP, PULL_EXISTS] >>
     strip_tac >> gvs[EVERY_MEM]) >>
  `event_decl_unique name tops` by
    gvs[body_inv_def, supported_program_def,
        supported_declaration_names_def, event_names_unique] >>
  gvs[body_inv_def, nsid_to_string_def, build_event_info_lookup_event_metadata_in,
      lookup_event_metadata_def, get_module_code_def, AllCaseEqs(),
      event_hash_def] >>
  metis_tac[scalar_abi_types_env]
QED

(* ===== The arguments ===== *)

(* The argument's explicit body-safety facts supply the call preconditions. *)
Theorem log_arg_body_pre[local]:
  !tops ctx cenv cx env e calls es.
    body_stmt_safe tops (Expr e) /\ ~is_extcode e /\
    body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
    well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, listTheory.EVERY_CONJ, GSYM expr_has_evm_run_def]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    fs[body_inv_def] >>
  `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es`, `calls`]
    irule stmt_expr_body_pre >> simp[] >> metis_tac[]
QED

(* Body safety and root allocation checks give each argument expr_body_pre;
   expression evaluation then preserves the invariant and types its value. *)
Theorem body_log_args_ready:
  !tops ctx func cenv cx env args.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args /\
    body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
    supported_pure_exprs tops args /\ well_typed_exprs env args /\
    ~supported_exprs_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
    call_evaluation_safe cx (int_calls_exprs args) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
              occurs_abi_decode_target target tops) ==>
    log_args_ready ctx func cenv cx (\es. expr_sim_inv cenv cx env es) args
Proof
  Induct_on `args` >> simp[log_args_ready_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `supported_pure_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_pure_expr_def]) >>
  qpat_x_assum `well_typed_exprs _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once well_typed_expr_def]) >>
  qpat_x_assum `~supported_exprs_exists _ _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
  qpat_x_assum `call_evaluation_safe _ _` (assume_tac o
    SIMP_RULE std_ss [Once int_calls_expr_def]) >>
  qpat_x_assum `!target. supported_exprs_exists _ _ ==> _` (strip_assume_tac o
    SIMP_RULE std_ss [Once supported_expr_exists_def, DISJ_IMP_THM,
                      FORALL_AND_THM]) >>
  gvs[body_exprs_ok_def] >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr h` >> simp[]) >>
  reverse conj_tac >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env h es` by
    (irule log_arg_body_pre >> simp[DE_MORGAN_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[body_expr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def, value_runtime_typed_def] >>
  `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
  gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]
QED

Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  rw[body_stmt_ok_def] >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            MAP expr_type es = MAP (SND o FST) fields` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  drule_all body_log_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields)
             (MAP (SND o FST) fields))) < dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields)
                (MAP (SND o FST) fields))) < dimword (:256)` by
    (gvs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
         allocLimitsTheory.log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env es /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv es` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) es` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  irule compile_log_stmt_frag >> simp[] >>
  conj_tac
  >- (qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `\s. expr_sim_inv cenv cx env s` >> simp[] >>
  irule body_log_args_ready >>
  gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  metis_tac[]
QED
