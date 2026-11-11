(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.  A case whose covered forms are proved dispatches the rest
 * to a cheated lemma marked RESIDUAL, whose comment names the premises
 * missing for the remaining forms.  The declarations, AnnAssign and For,
 * are in bodySimDeclCases, and Log in bodySimLog.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   body_*_other      — the residual forms of a case
 *   body_assign_local_memory — x = e for a local x held in memory
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *   body_stmt_safe    — the statement's no-EVM and internal-call facts;
 *                       allocation checks exclude bare .code roots
 *   reason_covered    — a reason compiles to a form the reason lemmas take
 *   supported_reason_code — a supported reason they don't take is an
 *                       immutable's, a pointer into code
 *   no_internal_call_int_calls, supported_pure_int_calls — no internal
 *                       call means int_calls_* = []
 *   expr_body_pre_eval_result, expr_body_pre_eval — evaluation keeps
 *                       expr_sim_inv and types the value
 *   type_widens_to_word — widening to a word type is equality
 *   expr_sim_inv_stmt  — expr_sim_inv after a statement, at the type
 *                        environment and compile environment it gives
 *   ce_locals_declared_declare_local, ce_locals_declared_stmt — the same
 *                        for ce_locals_declared
 *   locals_alloc_ok_extend, locals_alloc_ok_stmt — the same for
 *                        locals_alloc_ok
 *   compile_expr_open  — a supported expression that evaluates compiles
 *                        without terminating its block
 *   eval_stmts_popped_keys_indexed — statement evaluation keeps
 *                        popped_keys_indexed
 *
 * Helper:
 *   stmts_env_cs_mono, stmt_env_declare, declare_stmt_local_other,
 *   type_stmt_other    — stmt_env and type_stmt of a statement
 *   same_frame_trans, body_inv_same_frame, frame_ret_ok_same_frame,
 *   stmt_exprs_ok_same_frame, stmts_exprs_ok_EVERY — the frame facts
 *                        at a later compile env of the same body
 *   expr_sim_inv_push_scope — expr_sim_inv in a new scope
 *   body_inv_mcopy     — the frame's target has MCOPY
 *)

Theory bodySimStmtCases
Ancestors
  loweringStateRelDefs valueEncodingProps
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtSimIfCounted stmtSimAssert stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  bodyAssignPlace
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  stmtSimAssignTupleTargets
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain bodyStorageMetadata
  bodyAugAssignOther
Libs
  monadsyntax

(* ===== Helpers ===== *)

(* The two module facts stmt_expr_body_pre takes about cx_tops. *)
Theorem body_inv_cx_tops[local]:
  body_inv tops ctx cenv cx ==>
  cx_tops cx = tops /\
  (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
Proof
  strip_tac >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  fs[body_inv_def]
QED


(* ===== The compile environment after a statement ===== *)

(* compile_expr leaves its block open for a supported expression of the
   frame that evaluates.  Not every expression does: the lowering's
   fallbacks end their block in INVALID.  Which fallback a module variable
   takes depends on cenv.ce_module_vars, so the storage and transient bindings
   that state_rel gives are premises.  The induction is exprOpenMain's
   compile_expr_open_general. *)
Theorem compile_expr_open:
  !tops ctx cenv cx env e es tv es1 sa vv sb.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env e es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx e es = (INL tv, es1) /\
    compile_expr cenv (expr_type e) e sa = (vv, sb) /\
    ~block_is_terminated sa ==>
    ~block_is_terminated sb
Proof
  metis_tac[compile_expr_open_general]
QED

(* An assertion with no reason: stmtSimIf's compile_assert_frag. *)
Theorem body_assert_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e ak)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_expr_def] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag >> gvs[type_stmt_def] >>
  fs[body_expr_ok_def] >> metis_tac[compile_expr_grows]
QED

(* ===== Cases ===== *)

(* ===== Statements ===== *)

Theorem body_pass_case:
  !cx. body_stmt_ok cx Pass
Proof
  rw[body_stmt_ok_def, compile_pass_frag]
QED

Theorem body_continue_case:
  !cx. body_stmt_ok cx Continue
Proof
  rw[body_stmt_ok_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_def, stmt_framed_frag_def, gasContextTheory.gas_admissible_def,
          Once evaluate_def, raise_def, stmt_res_ok_def] >>
  irule compile_continue_frag
QED

Theorem body_break_case:
  !cx. body_stmt_ok cx Break
Proof
  rw[body_stmt_ok_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_def, stmt_framed_frag_def, gasContextTheory.gas_admissible_def,
          Once evaluate_def, raise_def, stmt_res_ok_def] >>
  irule compile_break_frag
QED

(* The frame's RetQ (frame_ret_ok). *)
Theorem body_return_none_case:
  !cx. body_stmt_ok cx (Return NONE)
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

Theorem body_return_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Return (SOME e))
Proof
  rw[body_stmt_ok_def, frame_ret_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* ===== Reasons ===== *)

(* The reason's compiled value is one the revert's encoder takes: a
   word or a memory buffer (stmtSimReasonExpr), or a storage or transient
   pointer (stmtSimReasonStorage). *)
Definition reason_covered_def:
  reason_covered cenv r <=>
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv)
End

Theorem well_typed_literal_string[local]:
  !ty s. well_typed_literal ty (StringL s) ==> ?n. ty = BaseT (StringT n)
Proof
  Cases >> simp[well_typed_literal_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[well_typed_literal_def]
QED

(* Only an internal call is lowered at a type its source type does not
   fix: the callee's declared return type. *)
Theorem lowered_value_type_not_call_word[local]:
  !cenv e. (!a t es d. e <> Call a t es d) /\ ~is_word_type (expr_type e) ==>
           ~is_word_type (lowered_value_type cenv e)
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >>
  rw[exprLoweringTheory.lowered_value_type_def, is_word_type_def, expr_type_def] >>
  simp[exprLoweringTheory.concat_buffer_type_def] >> rpt CASE_TAC >>
  gvs[is_word_type_def]
QED

(* A supported reason is a string expression (supported_string_reason),
   so it compiles to a memory or stack value, a storage or transient
   pointer, or a pointer into code (compile_expr_string_reason):
   expr_sim_inv holds each local through a variable pointer.  The first
   two are reason_covered. *)
Theorem supported_reason_code:
  !cenv cx env es tops e.
    expr_sim_inv cenv cx env es /\
    supported_string_reason tops e /\ well_typed_expr env e /\
    ~reason_covered cenv e ==>
    !sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
               reason_code_vv vv
Proof
  rpt gen_tac >> strip_tac >>
  `?n. expr_type e = BaseT (StringT n)` by
    (Cases_on `?t str. e = Literal t (StringL str)`
     >- (gvs[well_typed_expr_def, expr_type_def] >>
         metis_tac[well_typed_literal_string]) >>
     `case expr_type e of BaseT (StringT _) => T | _ => F` by
       (Cases_on `e` >> fs[supported_string_reason_def] >>
        rename1 `Literal _ lit` >> Cases_on `lit` >>
        fs[supported_string_reason_def]) >>
     Cases_on `expr_type e` >> fs[] >>
     rename1 `BaseT b` >> Cases_on `b` >> fs[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (irule lowered_value_type_not_call_word >>
     gvs[is_word_type_def] >> rpt strip_tac >>
     gvs[supported_string_reason_def, supported_pure_expr_def]) >>
  qspecl_then [`cenv`, `env`, `e`, `n`] mp_tac compile_expr_string_reason >>
  impl_tac >- (fs[expr_sim_inv_def] >> metis_tac[]) >>
  fs[reason_covered_def] >> metis_tac[]
QED

(* A reason read from an immutable, whose compiled value is a pointer into
   code (supported_reason_code): the revert's encoder copies it out of code
   (stmtSimReasonCode), the body being runtime code (body_inv).  A string
   literal goes to stmtSimReason. *)
Theorem body_raise_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Raise (RaiseReason e))) /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  rpt strip_tac >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag >> simp[]) >>
  irule compile_raise_code_reason_shared_frag >> gvs[] >> metis_tac[]
QED

(* A string literal reason (stmtSimReason), one whose compiled value
   reason_covered covers (stmtSimReasonExpr, stmtSimReasonStorage), or a
   pointer into code (body_raise_reason_other). *)
Theorem body_raise_reason_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Raise (RaiseReason e))
Proof
  rw[body_stmt_ok_def] >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag >> simp[]) >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_def, supported_raise_reason_def] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def,
         int_calls_raise_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  Cases_on `reason_covered cenv e`
  >- (gvs[reason_covered_def]
      >- (irule compile_raise_reason_frag >> simp[] >> metis_tac[])
      >- (irule compile_raise_storage_reason_frag >> simp[] >> metis_tac[])) >>
  irule body_raise_reason_other >> simp[] >>
  reverse conj_tac >-
    (conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule supported_reason_code >>
  gvs[supported_stmt_def, supported_raise_reason_def, type_stmt_def] >>
  metis_tac[]
QED

(* As body_raise_reason_other, after the condition fails. *)
Theorem body_assert_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e se es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assert e (AssertReason se)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Assert e (AssertReason se))) /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
                (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
              expr_vv_sim ctx func cenv cx (expr_type se) se es1) /\
    (!sa vv sb. compile_expr cenv (expr_type se) se sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  rpt strip_tac >>
  `expr_type e = BaseT BoolT` by gvs[type_stmt_def] >>
  Cases_on `?ml str. se = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_assert_reason_lit_frag >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  irule compile_assert_code_reason_shared_frag >> gvs[] >> metis_tac[]
QED

(* The reason simulates where the condition is false: both are pure, so
   the condition's evaluation keeps expr_sim_inv (expr_sim_pre_eval). *)
Theorem assert_reason_vv_sim[local]:
  !cx e se tops ctx func cenv env es es1.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_inv tops ctx cenv cx /\ expr_sim_pre cenv cx env e es /\
    well_typed_expr env se /\ int_calls_expr se = [] /\
    ~expr_has_evm_run se /\
    ~supported_expr_exists
       (\e. ~is_extcode e /\
            ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se /\
    ~is_extcode se /\ ~supported_expr_exists call_operands_effect_root se /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) se ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (do raw <- eval_expr cx e; read_result cx raw od) es =
      (INL (BoolV F), es1) ==>
    expr_vv_sim ctx func cenv cx (expr_type se) se es1
Proof
  rpt strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
  `?tv t. eval_expr cx e es = (INL tv, t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_ok cx se` by metis_tac[] >>
  `expr_body_pre cenv cx env se es1` by
    (simp[expr_body_pre_def] >> gvs[expr_sim_pre_def] >>
     CCONTR_TAC >> gvs[] >>
     qpat_x_assum `~supported_expr_exists (\e. ~is_extcode e /\ _) _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  metis_tac[body_expr_ok_def]
QED

(* As body_raise_reason_case, after compile_assert_frag's condition. *)
Theorem body_assert_reason_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e (AssertReason se))
Proof
  rw[body_stmt_ok_def] >>
  `supported_pure_expr tops e /\ supported_string_reason tops se` by
    gvs[supported_stmt_def, supported_assert_reason_def] >>
  `expr_type e = BaseT BoolT /\ well_typed_expr env e /\
   well_typed_expr env se` by gvs[type_stmt_def] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
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
  `~expr_has_evm_run se /\ ~is_extcode se /\
   ~supported_expr_exists call_operands_effect_root se` by
    simp[] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `int_calls_assert_reason (AssertReason se)` >> simp[]) >>
  `expr_sim ctx func cenv cx (BaseT BoolT) e es` by
    metis_tac[body_expr_ok_def] >>
  Cases_on `?ml str. se = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_assert_reason_lit_frag >> simp[] >>
      metis_tac[compile_expr_grows]) >>
  `int_calls_expr se = []` by
    (Cases_on `?t str. se = Literal t (StringL str)`
     >- gvs[int_calls_expr_def] >>
     `supported_pure_expr tops se` suffices_by
       metis_tac[supported_pure_int_calls] >>
     Cases_on `se` >> gvs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     gvs[supported_string_reason_def]) >>
  `!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
             (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
         expr_vv_sim ctx func cenv cx (expr_type se) se es1` by
    (rpt strip_tac >>
     qspecl_then [`cx`, `e`, `se`, `tops`, `ctx`, `func`, `cenv`, `env`,
                  `es with gas_obs := gs`, `es1`] mp_tac assert_reason_vv_sim >>
     disch_then irule >>
     drule_then strip_assume_tac body_inv_cx_tops >>
     gvs[expr_sim_pre_body, stmt_exprs_ok_def,
         supported_stmt_expr_exists_def, supported_assert_exists_def] >>
     metis_tac[expr_sim_pre_gas_obs]) >>
  Cases_on `reason_covered cenv se`
  >- (gvs[reason_covered_def]
      >- (irule compile_assert_reason_frag >> simp[] >> metis_tac[])
      >- (irule compile_assert_storage_reason_frag >> simp[] >>
          metis_tac[])) >>
  irule body_assert_reason_other >> simp[] >> rpt conj_tac
  >~ [`reason_code_vv`]
  >- (rpt gen_tac >> strip_tac >> irule supported_reason_code >> simp[] >>
      metis_tac[])
  >~ [`IS_SOME (type_stmt _ _ _)`] >- (qexists_tac `env` >> gvs[]) >>
  metis_tac[]
QED

(* An append to a storage or transient DynArray, the only target
   supported_append_target admits.  The helper adapter relates both writes. *)
Theorem body_append_storage_other:
  !cx nid e.
    (!s'' p t'. eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
                body_expr_ok cx e) ==>
    body_stmt_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `nid` >>
  rw[body_stmt_ok_def, supported_stmt_def, supported_append_target_def] >>
  irule body_append_storage_fragment >> metis_tac[supported_expr_def]
QED

(* supported_append_target admits no local, subscript or attribute target
   (#549, #559), so the storage root is the only form. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_append_storage_other >> first_assum ACCEPT_TAC) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_ok_def, supported_stmt_def, supported_append_target_def]
QED

(* ===== Assignments ===== *)

(* expr_sim_pre_eval_result and expr_sim_pre_eval under expr_body_pre
   (exprSimHyps' expr_body_pre_eval_result). *)
Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  `state_well_typed es' /\
   (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  gvs[] >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all expr_body_pre_eval_result >> simp[]
QED

(* expr_body_pre_eval for a run at any gas readings. *)
Theorem expr_body_pre_eval_gas[local]:
  !cenv cx env e es gs res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  rpt gen_tac >> strip_tac >> irule expr_body_pre_eval >>
  qexists_tac `es with gas_obs := gs` >> fs[]
QED

(* An assignment to a word local: stmtSimAssign's
   compile_assign_local_stmt_frag. *)
Theorem body_assign_local_word[local]:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (NameTarget id)) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[] >> metis_tac[type_widens_to_word]) >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  irule compile_assign_local_stmt_frag >> simp[] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs`, `INL v`,
               `es1`] mp_tac expr_body_pre_eval >>
  impl_tac >- fs[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `es1`, `id`, `expr_type e`] mp_tac
    expr_sim_inv_local >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[store_lays_out_typed]
QED

(* A storage declaration found by name is a variable declaration of tops
   under that name. *)

Theorem find_var_decl_storage_some:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED


(* expr_sim_inv's storage-variable clause from the program's frame: in a
   single-module program, a storage or transient variable has its declared
   type in ce_module_var_type and is not a mapping. *)
Theorem body_inv_storage_var_types:
  !tops ctx cenv cx.
    body_inv tops ctx cenv cx /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE) ==>
    !src id ts tr typ id_str.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME typ
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `src = NONE` by metis_tac[] >> gvs[body_inv_def] >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  drule_all build_maps_variable >> simp[]
QED

Theorem env_assignable_find_NONE:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

(* A supported scalar target is a word variable of tops in storage or
   transient storage. *)
Theorem supported_scalar_target_decl:
  !tops src id.
    supported_scalar_target tops (src, id) ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      is_word_type ty
Proof
  rpt gen_tac >> simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
  simp[is_word_type_def]
QED

(* An assignment to a word storage or transient variable:
   stmtSimAssignStorage's compile_assign_storage_typed_stmt_frag.  The
   typing finds the variable's declaration and layout slot, and body_inv's
   module clauses give cenv's view of it. *)
Theorem body_assign_toplevel_word[local]:
  !cx src id e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_scalar_target tops (src, id) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) =
      SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es
Proof
  rpt strip_tac >>
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE, id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> rename1 `FLOOKUP env.toplevel_vtypes _ = SOME (Type ty)` >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  irule compile_assign_storage_typed_stmt_frag >> simp[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot'` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  qexistsl_tac [`slot'`, `tvt`] >> simp[] >> rpt strip_tac >>
  drule_all expr_body_pre_eval_gas >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def]
QED

(* An assignment to a local in memory of the local's own type, a bytestring
   (a narrower one widens: Bytes[10] into Bytes[64]), or an empty value of a
   type with a length word: stmtSimAssignMem's
   compile_assign_local_memory_stmt_frag and the same for the widening and
   for the empty value, as stmtSimDeclMem's and stmtSimDeclEmpty's
   declarations.  The local's size is below 2 ** 64 (locals_alloc_ok), so
   its buffer and a bytestring copy's length word fit below 2 ** 256. *)
Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (NameTarget id)) e) /\
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
  drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
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

Theorem body_assign_local_memory:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (NameTarget id)) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops /\
   get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  drule_all body_assign_local_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `type_memory_bytes cenv ty = type_memory_size entry.type` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    metis_tac[locals_alloc_ok_def] >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (`has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
      irule compile_assign_local_empty_stmt_frag >> simp[] >>
      qexists_tac `ty` >> simp[] >>
      irule memory_rhs_empty_read_destination >> simp[] >>
      qexistsl_tac [`env`, `ty`] >> simp[]) >>
  `expr_type e = ty \/ is_bytestring_type ty` by metis_tac[] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty` by
    metis_tac[memory_rhs_destination_bound] >>
  `type_memory_size entry.type + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    decide_tac >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  drule expr_body_pre_type_evaluates >>
  disch_then (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_local_memory_widen_stmt_frag >> gns[] >>
  rpt conj_tac >>~- ([`val_footprint _ _ <= _`],
    rpt gen_tac >> strip_tac >> irule body_assign_local_memory_read >>
    conj_tac >- fs[] >>
    qexistsl_tac [`cx`, `env`, `es with gas_obs := gs`, `es1`, `id`, `tops`,
                  `ty`] >>
    fs[] >> metis_tac[type_widens_to_def]) >>
  metis_tac[type_widens_to_def, arg_type_fits_bytestring_source]
QED

(* An assignment to a word field of a local struct: stmtSimAssignAttr's
   compile_assign_attr_local_case. *)
Theorem body_assign_attr_local[local]:
  !cx id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es' sid
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) =
      SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (Cases_on `type_place_target env (AttributeTarget (NameTarget id) fld)` >>
     gvs[type_stmt_def, atarget_accepts_def] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[type_widens_to_word]) >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx fty e es` by metis_tac[body_expr_ok_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (fty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  irule compile_assign_attr_local_case >> simp[] >> metis_tac[]
QED

(* A struct field write the supported subset admits is to a storage or
   transient struct of the main module, tops. *)
Theorem supported_storage_field_write_decl:
  !tops src id fld.
    supported_storage_field_write tops (src, id) fld ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  rpt gen_tac >>
  simp[supported_storage_field_write_def,
       supportedExprFormsTheory.supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >> simp[] >>
  metis_tac[find_var_decl_storage_some]
QED

(* An assignment to a word field of a storage or transient struct:
   stmtSimAssignAttrStorage's compile_assign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot, the typing finds
   its declaration and layout slot, and body_inv's module clauses give
   cenv's view of it. *)
Theorem body_assign_attr_storage[local]:
  !cx src id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es'
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_place_target env
      (AttributeTarget (TopLevelNameTarget (src, id)) fld) =
      SOME (Type fty) /\
    is_word_type fty /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld)) e)) es
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def] >>
     metis_tac[type_widens_to_word]) >>
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (expr_type e, fsz)` by
    metis_tac[attribute_type_struct_field] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_case >> simp[] >> metis_tac[]
QED

Theorem body_assign_copy_rhs_pre[local]:
  !tops ctx cenv cx e env es ret_ty nsid env'.
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
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
  drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def,
      int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem body_assign_copy_region[local]:
  !cx mid id tr off tvt.
    storage_layout_safe cx /\
    storage_var_info cx mid id = SOME (tr,off,tvt) /\
    0 < type_slot_size tvt ==>
    off + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
      (k',tv') <> (n2w off,tvt) ==>
      ranges_disjoint off (type_slot_size tvt) (w2n k') (type_slot_size tv'))
Proof
  rpt gen_tac >> strip_tac >>
  `off + type_slot_size tvt <= dimword (:256)` by
    (drule storage_layout_safe_layout >>
     simp[well_formed_layout_def] >> metis_tac[]) >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : 256 word) = off` by simp[] >>
  drule declared_storage_region_ordinary >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `(mid,id,[]) <> (mid',n',subs')` by
    (strip_tac >> gvs[]) >>
  drule_all storage_layout_safe_region_separation >> simp[]
QED

Theorem body_assign_copy_target[local]:
  !tops ctx cenv cx src id mut ty ast_slot env es ret_ty e env'.
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME ast_slot) /\
    (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
      SOME env' ==>
    src = NONE /\ get_module_code cx NONE = SOME tops /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ty /\
    ?tr id_str off tvt.
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
      lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
      evaluate_type (get_tenv cx) ty = SOME tvt
Proof
  rpt gen_tac >> strip_tac >> (
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[])
QED

Theorem storage_scalar_fit_equal[local]:
  !tops fuel t u.
    supported_scalar_type t /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  Cases_on `t` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `u` >>
  simp[arg_type_fits_def] >>
  rename1 `arg_type_fits _ (BaseT ub)` >>
  Cases_on `bt` >> Cases_on `ub` >>
  simp[supported_word_type_def, supported_string_type_def,
       arg_type_fits_def, Once supported_nested_type_def,
       supported_full_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  gvs[arg_type_fits_def, supported_word_type_def, supported_string_type_def]
QED

Theorem storage_scalars_fit_equal[local]:
  !ts us tops fuel.
    EVERY supported_scalar_type ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> drule_all storage_scalar_fit_equal >> strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem storage_value_fit_equal[local]:
  !tops t u.
    supported_value_type tops t /\ supported_storage_type tops u /\
    (!et n. u <> ArrayT et (Dynamic n)) /\ arg_type_fits t u ==> t = u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `supported_scalar_type t`
  >- metis_tac[storage_scalar_fit_equal, supported_storage_type_def] >>
  Cases_on `t` >>
  gvs[supported_value_type_def] >> Cases_on `u` >>
  gvs[arg_type_fits_def]
  >~ [`arg_types_fit ts us`]
  >- (gvs[supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def] >>
      metis_tac[storage_scalars_fit_equal]) >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
  fs[supported_storage_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def, supported_full_word_type_def] >>
  strip_tac >>
  metis_tac[storage_scalar_fit_equal, supported_scalar_type_def]
QED

Theorem storage_not_bytestring[local]:
  !tops t. supported_storage_type tops t ==> ~is_bytestring_type t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def, supported_storage_type_def,
       Once supported_nested_type_def, supported_full_word_type_def]
QED

Theorem storage_rhs_lowered_type[local]:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >> rpt conj_tac
  >- (simp[expr_type_def] >> metis_tac[storage_not_bytestring, is_bytestring_type_def])
  >- (simp[expr_type_def] >> metis_tac[storage_not_bytestring, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def, expr_type_def] >>
      strip_tac >> gvs[expr_type_def] >>
      drule storage_not_bytestring >>
      gvs[well_typed_builtin_app_def, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def,
           type_builtin_result_ok_def, expr_type_def] >> strip_tac >>
      gvs[expr_type_def] >>
      drule storage_not_bytestring >> simp[is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      rename1 `Call ct (IntCall func_id) cargs cdflt` >>
      `supported_program tops /\
       cenv.ce_func_return_type = build_func_return_type tops /\
       get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      `well_typed_expr env (Call ct (IntCall func_id) cargs cdflt)` by
        gvs[expr_body_pre_def] >>
      qpat_x_assum `supported_expr _ _` mp_tac >>
      simp[supported_expr_def, supported_pure_expr_def,
           supported_effect_expr_def] >> strip_tac >>
      Cases_on `cdflt` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
      PairCases_on `x` >>
      `?sig. FLOOKUP env.fn_sigs func_id = SOME sig` by
        (Cases_on `func_id` >>
         gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
      drule_all supported_internal_signature_return >> strip_tac >>
      drule_all supported_internal_return_admissible >> strip_tac >>
      drule_all supported_internal_return_type >> strip_tac >>
      qpat_x_assum `well_typed_expr _ _` mp_tac >>
      Cases_on `func_id` >>
      simp[well_typed_expr_def, expr_type_def] >> strip_tac >>
      gvs[exprLoweringTheory.lowered_value_type_def, expr_type_def] >>
      gvs[supported_return_type_def, type_widens_to_def]
      >- (Cases_on `ct` >> gvs[arg_type_fits_def]) >>
      metis_tac[storage_value_fit_equal]) >>
  simp[exprLoweringTheory.lowered_value_type_def]
QED

(* An assignment to a private storage or transient variable of a type that
   is not a word, not a DynArray and not empty, from a value of exactly that
   type: stmtSimAssignStorageCopy's compile_assign_storage_copy_stmt_frag.
   The region separation it asks for comes from storage_layout_safe in
   expr_sim_inv. *)
Theorem body_assign_toplevel_copy[local]:
  !cx nsid e tops ctx func cenv env env' ret_ty lctx RetQ es res es' mut ty
   slot.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
    supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> Cases_on `nsid` >>
  rename1 `supported_variable_decl tops (src,id)` >> strip_tac >> (
  drule_at (Pos (el 2)) body_assign_copy_target >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all body_assign_copy_rhs_pre >> strip_tac >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> strip_tac >>
  `0 < type_slot_size tvt` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `storage_layout_safe cx /\ env_consistent env cx es` by
    fs[expr_sim_inv_def] >>
  `storage_var_info cx NONE id = SOME (tr,off,tvt)` by
    simp[storage_var_info_def] >>
  drule_all body_assign_copy_region >> strip_tac >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ok_def] >>
  `!ann t args. e = TypeBuiltin ann Empty t args ==> t = expr_type e` by
    (rpt strip_tac >> gvs[type_stmt_def, atarget_accepts_def,
       well_typed_expr_def, type_builtin_result_ok_def, expr_type_def,
       AllCaseEqs()]) >>
  `supported_storage_type tops (expr_type e)` by
    (`supported_program tops` by fs[body_inv_def] >>
     drule supported_variable_decl_mem >> strip_tac >>
     drule_all supportedProgramTheory.supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule_all storage_rhs_lowered_type >> simp[]) >>
  irule compile_assign_storage_copy_stmt_frag >> asm_rewrite_tac[] >>
  qexistsl_tac [`id_str`, `off`, `tr`, `tops`, `tvt`, `expr_type e`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def])
QED

(* A local assigned to takes memory: its type is a widening of the assigned
   value's type, which is assignable. *)
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

(* RESIDUAL (#767): a place assigned a value whose lowered type is
   neither e's type nor a bytestring type e's fits: an internal call whose
   return type widens to the call's type (type_widens_to: a DynArray of a
   smaller bound, a tuple elementwise), as body_assign_widened_aggregate_call
   for a local, at any place. *)
Theorem body_assign_place_widened_aggregate_call:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
                (Assign (BaseTarget t) e) ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

(* The other base targets, by bodyAssignPlace's general place root (the
   target's pointer, then a store at its location), except for a value
   whose lowered type differs from its own (above). *)
Theorem body_assign_other:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
                (Assign (BaseTarget t) e) ==>
              occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    body_stmt_safe tops (Assign (BaseTarget t) e) /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt strip_tac >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
            is_bytestring_type (expr_type e) /\
            is_bytestring_type (lowered_value_type cenv e) /\
            arg_type_fits (lowered_value_type cenv e) (expr_type e)`
  >- (irule bodyAssignPlaceTheory.body_assign_place_case >> metis_tac[]) >>
  irule body_assign_place_widened_aggregate_call >> metis_tac[]
QED

(* RESIDUAL (#767): a memory-backed local assigned an internal call whose
   return type widens to the call's type other than as a bytestring
   (type_widens_to: a DynArray of a smaller bound, a tuple elementwise). *)
Theorem body_assign_widened_aggregate_call:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

Theorem body_assign_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (BaseTarget t) e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    is_word_type ty`
  >- (gvs[] >> irule body_assign_local_word >> metis_tac[]) >>
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    ~is_word_type ty /\
                    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
                     is_bytestring_type ty \/
                     has_length_word (expr_type e) /\ is_empty_value_expr e)`
  >- (`!id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty ==>
              0 < type_memory_bytes cenv ty` by
        (rpt strip_tac >> gvs[] >>
         metis_tac[assign_local_memory_bytes_pos]) >>
      Cases_on `(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e))`
      >- (gvs[] >>
          irule body_assign_local_memory >> metis_tac[]) >>
      gvs[] >> irule body_assign_widened_aggregate_call >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_toplevel_word >> metis_tac[]) >>
  Cases_on `?nsid mut ty slot.
              t = TopLevelNameTarget nsid /\
              supported_variable_decl tops nsid =
                SOME (Private, mut, ty, SOME slot) /\
              (mut = Storage \/ mut = Transient) /\
              ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
              0 < type_memory_bytes cenv ty /\ expr_type e = ty`
  >- (gvs[] >> irule body_assign_toplevel_copy >> metis_tac[]) >>
  Cases_on `?id fld sid fty.
              t = AttributeTarget (NameTarget id) fld /\
              FLOOKUP env.var_types id = SOME (StructT sid) /\
              attribute_type env.type_defs (StructT sid) fld = SOME fty /\
              is_word_type fty`
  >- (gvs[] >> irule body_assign_attr_local >> metis_tac[]) >>
  Cases_on `?nsid fld fty.
              t = AttributeTarget (TopLevelNameTarget nsid) fld /\
              supported_storage_field_write tops nsid fld /\
              type_place_target env t = SOME (Type fty) /\ is_word_type fty`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_assign_attr_storage >> metis_tac[]) >>
  irule body_assign_other >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >> fs[] >> metis_tac[]
QED

(* Both lowering entry points check that the target supports MCOPY. *)
Theorem body_inv_mcopy:
  !tops ctx cenv cx. body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[vyperCompilerTheory.run_deploy_lowering_def, AllCaseEqs(),
          vyperCompilerTheory.lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperCompilerTheory.run_lowering_def, AllCaseEqs(),
      vyperCompilerTheory.lowering_policy_ok_def]
QED

(* A local of a tuple target, of a type with a size that is not 0: held
   through a pointer at its own type, and if in memory, with a size below
   2 ** 64 (locals_alloc_ok), so a bytestring copy's 64 bytes of rounding
   fit below 2 ** 256. *)
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

(* After the source is read, a local of a tuple target holds a value of its
   own type: a word as stored, otherwise at the type its pointer has. *)
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

(* The buffer a tuple assignment stages a memory view's value in fits
   below 2 ** 256: alloc_limits_stmt bounds it by 2 ** 64. *)
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
    metis_tac[allocation_limit_word_room] >>
  decide_tac
QED

(* A tuple of locals of types with sizes that are not 0 (a word's is 32):
   stmtSimAssignTupleMem's compile_assign_tuple_locals_memory_stmt_frag.
   The target has MCOPY (body_inv_mcopy). *)
Theorem body_assign_tuple_locals[local]:
  !cx ids e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    body_stmt_safe tops (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
         assignable_type (get_tenv cx) (TupleT tys) /\
         LENGTH tys = LENGTH ids /\
         !i. i < LENGTH ids ==>
             FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by
    gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
        LIST_REL_EL_EQN, EL_MAP, well_typed_target_def,
        well_typed_expr_def, AllCaseEqs()] >>
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
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def,
       optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ret_ty`, `ids`,
               `e`, `es`, `tys`, `tvs`] mp_tac
    compile_assign_tuple_locals_memory_stmt_frag >>
  disch_then irule >> rpt conj_tac
  >~ [`expr_sim _ _ _ _ _ _ _`] >- metis_tac[body_expr_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound >> metis_tac[])
  >~ [`FLOOKUP cenv.ce_vars _`]
  >- (rpt strip_tac >>
      `FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by simp[] >>
      `0 < type_memory_bytes cenv (EL i tys)` by
        (qpat_x_assum `EVERY _ ids` mp_tac >> simp[EVERY_EL] >>
         disch_then drule >> strip_tac >> gvs[]) >>
      irule tuple_target_local_ptr >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`store_lays_out _ _ _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      `value_has_type (EL i tvs) (EL i vs)` by
        gvs[value_runtime_typed_def, value_has_type_def,
            values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
      irule tuple_target_local_lays_out >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      gvs[value_runtime_typed_def]) >>
  fs[]
QED

(* The locals a tuple is assigned to take memory: their types are the
   tuple's element types, which are assignable, so they take a storage slot
   (assignable_type_slot_size_pos). *)
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
    gvs[well_typed_atarget_def, well_typed_target_def, vyperTypeEnvTheory.type_place_target_NameTarget,
        AllCaseEqs()] >>
  `assignable_type env.type_defs ty` by metis_tac[EVERY_EL] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

Theorem body_assign_tuple_rhs_pre[local]:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  body_stmt_safe tops (Assign (TupleTarget gs) e) /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
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
  drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem body_tuple_target_local_aligned:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv
Proof
  rpt strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_local] >>
  metis_tac[expr_sim_inv_local]
QED

Theorem body_tuple_target_local_layout:
  expr_sim_inv cenv cx env es /\
  well_typed_atarget env (BaseTarget (NameTarget id)) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v
Proof
  rpt strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def,
      vyperTypeEnvTheory.type_place_target_NameTarget] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `entry.type = tv` by metis_tac[expr_sim_inv_local, optionTheory.SOME_11] >>
  simp[tupleTargetStorePropsTheory.tuple_target_layout_local] >>
  metis_tac[store_lays_out_typed]
QED

Theorem body_tuple_target_local_room:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

Theorem body_tuple_target_toplevel_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops nsid /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget nsid)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `is_word_type declared_ty` >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) = build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `declared_ty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_toplevel] >>
  rpt strip_tac >> irule accountsRelPropsTheory.storage_dead_update_word_region >>
  qexistsl_tac [`NONE`, `id`, `[]`, `tv`] >>
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED

Theorem body_tuple_target_field_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_storage_field_write tops nsid fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
    SOME (Type ty) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx
    (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[] >>
  drule_all attribute_type_struct_field >> strip_tac >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  drule_all exprSimFieldLayoutTheory.struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all exprSimAttributeFieldsTheory.struct_field_type >> strip_tac >> gvs[] >>
  drule vyperPlaceResultTypingTheory.struct_field_slot_exists >> strip_tac >>
  drule_all exprSimFieldLayoutTheory.struct_field_offset_slots_eq >> strip_tac >>
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_field] >>
  rpt gen_tac >> irule accountsRelPropsTheory.storage_dead_update_struct_word_field >>
  goal_assum (drule_at Any) >> qexistsl_tac [`NONE`, `id`] >>
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED

Theorem body_tuple_target_ready:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  locals_alloc_ok cenv env /\ well_typed_atarget env g ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ((?id lty. g = BaseTarget (NameTarget id) /\
            FLOOKUP env.var_types id = SOME lty /\
            0 < type_memory_bytes cenv lty) \/
   (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
           supported_scalar_target tops nsid) \/
   (?nsid fld fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      supported_storage_field_write tops nsid fld /\
      type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
        SOME (Type fty) /\ is_word_type fty)) ==>
  tuple_target_aligned cenv cx g ty tv /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  (!es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type tv v ==>
     tuple_target_layout es1.scopes g ty tv v)
Proof
  rpt strip_tac >> gvs[tupleTargetStorePropsTheory.tuple_target_base_type]
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      irule body_tuple_target_local_aligned >> metis_tac[])
  >- (gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
      metis_tac[body_tuple_target_local_room])
  >- (irule body_tuple_target_local_layout >>
      simp[well_typed_atarget_def, well_typed_target_def] >> metis_tac[])
  >- (irule body_tuple_target_toplevel_aligned >> metis_tac[])
  >- (drule_all body_tuple_target_toplevel_aligned >>
      Cases_on `nsid` >>
      simp[tupleTargetStorePropsTheory.tuple_target_aligned_toplevel])
  >- simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
  >- (irule body_tuple_target_field_aligned >> metis_tac[])
  >> simp[tupleTargetStorePropsTheory.tuple_target_layout_def]
QED

(* Every element of the tuple is a local of a size that is not 0, a word
   storage or transient variable, or a word field of a storage or transient
   struct, mixed in any order (an empty tuple is not assignable_type, so it
   does not type-check).  The lowering loads
   every element before it stores any (compile_tuple_unpack); each store
   evaluates its target (compile_get_target_ptr) right before it, as the
   source evaluates each element's place right before its write
   (assign_tuple_target_list). *)
Theorem body_assign_tuple_targets[local]:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    body_stmt_safe tops (Assign (TupleTarget gs) e) /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt strip_tac >>
  irule stmtSimAssignTupleTargetsTheory.stmt_frag_storage_maps_intro >> strip_tac >>
  drule tupleTargetStorePropsTheory.tuple_targets_typing >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule body_assign_tuple_rhs_pre >> metis_tac[]) >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH] >>
  `!i. i < LENGTH gs ==>
     tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
     (~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
     !es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type (EL i tvs) v ==>
       tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) v` by
    (qx_gen_tac `i` >> disch_tac >> irule body_tuple_target_ready >>
     fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `gs <> []` by (strip_tac >> gvs[assignable_type_def]) >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ret_ty`, `gs`,
               `e`, `es`, `tys`, `tvs`] mp_tac
    stmtSimAssignTupleTargetsTheory.compile_assign_tuple_targets_stmt_frag >>
  disch_then irule >> rpt conj_tac
  >~ [`expr_sim _ _ _ _ _ _ _`] >- metis_tac[body_expr_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound >> metis_tac[])
  >~ [`tuple_target_layout _ _ _ _ _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      gvs[value_runtime_typed_def, value_has_type_def,
          values_have_types_LIST_REL, LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      gvs[value_runtime_typed_def])
  >> metis_tac[]
QED

(* RESIDUAL (#637 tuple assignments): the other tuple targets, each with
   an element body_assign_tuple_targets leaves.
   - A local of size 0 next to a storage element: there is none (a
     tuple element's type is assignable, assign_tuple_locals_bytes_pos), but
     the case split doesn't show it yet.
   - A subscript element (a storage array or mapping): its target's place
     needs the subscript step of the target/place judgment
     (targetPlaceSimCases' target_subscript_case), not proved yet.
   - A field of a storage or transient struct that is not a word: the
     copy of an aggregate into storage, as for Assign (body_assign_other).
   - An immutable: the lowering keeps it in code (LocCode), which nothing
     relates to the source's immutables yet (targetPlaceSim's
     immutable_root).
   A nested TupleTarget is not supported (supported_assignment). *)
Theorem body_assign_tuple_other:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL (#767): a tuple target assigned an internal call whose return
   type widens to the call's type (type_widens_to: a tuple elementwise), so
   the tuple is unpacked at the callee's return type. *)
Theorem body_assign_tuple_widened_call[local]:
  !cx gs e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

Theorem body_assign_tuple_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (TupleTarget gs) e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  reverse (Cases_on `lowered_value_type cenv e = expr_type e`)
  >- (irule body_assign_tuple_widened_call >> metis_tac[]) >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (gvs[] >> drule_all assign_tuple_locals_bytes_pos >> strip_tac >>
      `EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) ids` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      irule body_assign_tuple_locals >> metis_tac[]) >>
  Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                                FLOOKUP env.var_types id = SOME ty /\
                                0 < type_memory_bytes cenv ty) \/
                       (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                               supported_scalar_target tops nsid) \/
                       (?nsid fld fty.
                          g = BaseTarget
                                (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                          supported_storage_field_write tops nsid fld /\
                          type_place_target env
                            (AttributeTarget (TopLevelNameTarget nsid) fld) =
                            SOME (Type fty) /\ is_word_type fty)) gs`
  >- (irule body_assign_tuple_targets >> metis_tac[]) >>
  irule body_assign_tuple_other >> metis_tac[]
QED

(* ===== Augmented assignments ===== *)

(* x op= e on a local: stmtSimAugAssign's compile_augassign_local_case,
   the operand's internal calls allowed. *)
Theorem body_augassign_local[local]:
  !cx ty id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    body_stmt_safe tops (AugAssign ty (NameTarget id) bop e) /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
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
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `FLOOKUP env.var_types id = SOME ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         DISJ_IMP_THM, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types id` >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `body_expr_ok cx e` by
    (first_x_assum irule >> metis_tac[eval_target_place_local]) >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[body_expr_ok_case] >>
  irule compile_augassign_local_case >> simp[DISJ_IMP_THM] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `F` >> simp[]
QED

(* x.f op= e on a field of a local struct: stmtSimAugAssignAttr's
   compile_augassign_attr_local_case.  The typing makes f's type a word
   (well_typed_binop_augassign_word), and x.f is read wherever
   expr_sim_inv holds (augassign_attr_local_place), which gives e's
   judgment. *)
Theorem body_augassign_attr_local[local]:
  !cx ty id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) =
      SOME env' /\
    body_stmt_safe tops (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
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
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?sid. FLOOKUP env.var_types id = SOME (StructT sid) /\
         attribute_type env.type_defs (StructT sid) fld = SOME ty /\
         well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\
         bop <> NotIn` by
    (gvs[type_stmt_def, well_typed_target_def,
         vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     rename1 `attribute_type _ tgt_ty fld = SOME _` >>
     Cases_on `tgt_ty` >> gvs[attribute_type_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (ty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `body_expr_ok cx e` by
    (drule_all augassign_attr_local_place >> strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  `(bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL \/ bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_expr_def, DISJ_IMP_THM, AllCaseEqs()] >>
  irule compile_augassign_attr_local_case >> simp[] >> metis_tac[]
QED

(* self.x op= e on a word storage or transient variable:
   stmtSimAugAssignStorage's compile_augassign_toplevel_case.  The typing
   finds x's declaration, and body_inv's module clauses give cenv's view of
   it, as for body_assign_toplevel_word; x's place is read wherever
   expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_toplevel_word[local]:
  !cx ty src id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (TopLevelNameTarget (src, id)) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_scalar_target tops (src, id) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    body_stmt_safe tops (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
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
  drule supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `MEM (VariableDecl vis mut id dty init) tops` >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE, id)) = SOME (Type ty) /\
   well_typed_expr env e /\ assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _, _)` >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     TRY (conj_tac >-
          gvs[listTheory.EVERY_MEM, optionTheory.IS_SOME_EXISTS]) >>
     qexists_tac `[]` >> simp[]) >>
  `?v0. read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es)` by
    (irule exprSimTopLevelPropsTheory.toplevel_storage_read_decodes >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all eval_target_place_toplevel >> strip_tac >>
  `body_expr_ok cx e` by
    (first_x_assum irule >> simp[read_place_def] >> metis_tac[]) >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[body_expr_ok_case] >>
  irule compile_augassign_toplevel_case >> simp[DISJ_IMP_THM] >>
  conj_tac
  >- (qexists_tac `env` >> simp[] >>
      metis_tac[assignable_type_well_formed]) >>
  qexists_tac `F` >> simp[]
QED

(* self.x.f op= e on a word field of a storage or transient struct:
   stmtSimAugAssignAttrStorage's compile_augassign_attr_storage_case.  The
   supported subset puts the struct in tops with a slot and the typing finds
   its declaration, as for body_assign_attr_storage; x.f's slot is read
   wherever expr_sim_inv holds, which gives e's judgment. *)
Theorem body_augassign_attr_storage[local]:
  !cx ty src id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx
         (AttributeTarget (TopLevelNameTarget (src, id)) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    supported_storage_field_write tops (src, id) fld /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      = SOME env' /\
    body_stmt_safe tops (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop
         e) /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld)
            bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)) es
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
  drule supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?tgt_ty. type_place_target env (TopLevelNameTarget (NONE, id)) =
              SOME (Type tgt_ty) /\
            attribute_type env.type_defs tgt_ty fld = SOME ty /\
            well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\
            bop <> NotIn` by
    gvs[type_stmt_def, well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_AttributeTarget, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (ty, fsz)` by
    metis_tac[attribute_type_struct_field] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME lslot` >>
  `body_expr_ok cx e` by
    (drule_all augassign_attr_storage_place >> strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `expr_sim ctx func cenv cx ty e es` by metis_tac[body_expr_ok_def] >>
  `(bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL \/ bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_expr_def, DISJ_IMP_THM, AllCaseEqs()] >>
  irule compile_augassign_attr_storage_case >> simp[] >> metis_tac[]
QED

(* RESIDUAL (#637 augmented assignment): the targets other than a local, a
   field of a local struct, a word storage or transient variable
   (supported_scalar_target), or a word field of a storage or transient
   struct (supported_storage_field_write).
   - A field of a storage or transient struct the supported subset does
     not admit: no statement lemma.
   - An immutable (supported_target's supported_immutable_type): no
     statement lemma.
   - A field of a field or of a subscript: no statement lemma (the
     simulation of compile_get_target_ptr on eval_target_place).
   - Subscript targets: no statement lemma (#851). *)
Theorem body_augassign_other:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    body_stmt_safe tops (AugAssign ty t bop e) /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  rpt strip_tac >> irule body_augassign_other_leaf >> metis_tac[]
QED

Theorem body_augassign_case:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t ==>
    body_stmt_ok cx (AugAssign ty t bop e)
Proof
  rw[body_stmt_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  Cases_on `?id. t = NameTarget id`
  >- (gvs[] >> irule body_augassign_local >> metis_tac[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_toplevel_word >> metis_tac[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (gvs[] >> irule body_augassign_attr_local >> metis_tac[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (gvs[] >> rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule body_augassign_attr_storage >> metis_tac[]) >>
  irule body_augassign_other >> metis_tac[]
QED

(* stmtSimIf's compile_if_stmt_frag, with the branches' judgments at the
   pushed scope. *)
Theorem body_if_case:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ok cx ss2) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ok_def] >>
  rpt gen_tac >> strip_tac >>
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
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  fs[GSYM optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim ctx func cenv cx ty e es /\
        expr_vv_sim ctx func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_ok_def]) >>
     disch_then irule >> conj_tac
     >- (qexists_tac `tops` >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  irule compile_if_stmt_frag >> simp[stmts_env_cs_mono] >>
  conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `?tv s1. eval_expr cx e (es with gas_obs := gs) = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_ok cx ss1 /\ body_stmts_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >>
     metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval_gas >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def, alloc_limits_stmt_def,
      stmt_valued_return_def, GSYM optionTheory.IS_SOME_EXISTS, listTheory.EVERY_CONJ] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

(* stmtSim's compile_expr_stmt_frag_ok, given the expression's
   expr_vv_sim (the IH) and compile_expr_open. *)
Theorem body_expr_stmt_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Expr e)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ok_def] >>
  rpt gen_tac >> strip_tac >>
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
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac body_inv_cx_tops >>
     irule stmt_expr_body_pre >> simp[] >> qexists_tac `[]` >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e) e es /\
   expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_ok_def]) >>
     disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`,
                              `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  irule compile_expr_stmt_frag_ok >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  metis_tac[compile_expr_open]
QED

(* ===== Statement lists ===== *)

Theorem body_stmts_nil_case:
  !cx. body_stmts_ok cx []
Proof
  rw[body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff, stmt_frag_nil]
QED

(* stmtSim's stmt_frag_cons_env: the head by the IH, the tail by the IH at
   the environments the head's typing and declaration give. *)
Theorem body_stmts_cons_case:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ok cx ss) /\
    body_stmt_ok cx s ==>
    body_stmts_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def,
      supported_stmt_expr_exists_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule stmt_frag_cons_env >>
  simp[cj 1 compile_stmt_cs_mono, stmts_env_cs_mono] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmt_ok _ _` (irule o REWRITE_RULE [body_stmt_ok_def, body_stmt_safe_def, body_stmts_safe_iff]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmt_exprs_ok c = stmt_exprs_ok cenv` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[expr_sim_inv_gas_obs, call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by
    metis_tac[body_inv_same_frame] >>
  `frame_ret_ok ctx func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_same_frame] >>
  qpat_x_assum `!s'' t. _ ==> body_stmts_ok _ _` drule >>
  simp[body_stmts_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED
