(*
 * The body simulation of S1: statement cases (#637)
 *
 * One lemma for each statement case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  Those marked GAP are
 * cheated; their comments name the existing lemmas they dispatch to and
 * what is left.  A case whose covered forms are proved dispatches the rest
 * to a cheated lemma marked RESIDUAL, whose comment names the premises
 * missing for the remaining forms.
 *
 * TOP-LEVEL:
 *   body_*_case       — one case of the induction each
 *   body_*_other      — the residual forms of a case
 *   stmt_expr_body_pre — a statement's expression meets expr_body_pre
 *   reason_covered    — a reason compiles to a form the reason lemmas take
 *   no_internal_call_int_calls, supported_pure_int_calls — no internal
 *                       call means int_calls_* = []
 *   expr_body_pre_eval_result, expr_body_pre_eval — evaluation keeps
 *                       expr_sim_inv and types the value
 *   type_widens_to_word — widening to a word type is equality
 *)

Theory bodySimStmtCases
Ancestors
  list bodySim exprSim exprSimHyps exprLoweringProps stmtSim stmtSimIf
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix compileEnv exprSimMain
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple

(* ===== Helpers ===== *)

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  simp[expr_body_pre_def] >> metis_tac[call_evaluation_safe_append_left]
QED

(* An assertion with no reason: stmtSimIf's compile_assert_frag. *)
Theorem body_assert_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_ok cx e ==>
    body_stmt_ok cx (Assert e ak)
Proof
  rw[body_stmt_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
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
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[compile_pass_frag]
QED

Theorem body_continue_case:
  !cx. body_stmt_ok cx Continue
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_continue_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
QED

Theorem body_break_case:
  !cx. body_stmt_ok cx Break
Proof
  rw[body_stmt_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, raise_def] >> rw[] >>
  Cases_on `lctx` >> simp[compile_break_frag] >>
  simp[stmt_frag_def, stmt_res_ok_def]
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
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* ===== Reasons ===== *)

(* An expression with no internal call in it has no internal calls to
   make.  Reasons and conditions are pure (supported_pure_no_internal_call). *)
Theorem no_internal_call_int_calls:
  (!e. ~supported_expr_exists expr_internal_call_root e ==>
       int_calls_expr e = []) /\
  (!t. ~supported_target_exists expr_internal_call_root t ==>
       int_calls_target t = []) /\
  (!es. ~supported_exprs_exists expr_internal_call_root es ==>
        int_calls_exprs es = []) /\
  (!eo. ~supported_opt_exists expr_internal_call_root eo ==>
        int_calls_opt eo = []) /\
  (!kes. ~supported_fields_exists expr_internal_call_root kes ==>
         int_calls_named_exprs kes = [])
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def, supported_expr_exists_def,
     expr_internal_call_root_def]
QED

Theorem supported_pure_int_calls:
  !tops e. supported_pure_expr tops e ==> int_calls_expr e = []
Proof
  metis_tac[supported_pure_no_internal_call, expr_has_internal_call_def,
            no_internal_call_int_calls]
QED

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

(* RESIDUAL (#637 raise/assert with a reason): a reason whose compiled
   value reason_covered does not cover.  Expected unreachable: only an
   immutable compiles to another form (LocCode, compile_expr's TopLevelName
   case), and a supported program declares none
   (supported_immutables_constants_rejected); a supported TopLevelName
   names a storage or transient variable, which storage_vars_rel places in
   storage.  Proving it needs that argument, not a new reason lemma. *)
Theorem body_raise_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Raise (RaiseReason e))) /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Raise (RaiseReason e)) es = (res, es') /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    ~reason_covered cenv e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e))) es res es'
Proof
  cheat
QED

(* A string literal reason (stmtSimReason), or one whose compiled value
   reason_covered covers (stmtSimReasonExpr, stmtSimReasonStorage). *)
Theorem body_raise_reason_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Raise (RaiseReason e))
Proof
  rw[body_stmt_ok_def] >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
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
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* RESIDUAL (#637 raise/assert with a reason): as body_raise_reason_other,
   after the condition fails. *)
Theorem body_assert_reason_other:
  !ctx func cx lctx RetQ cenv tops bindings env ret_ty e se es res es'.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assert e (AssertReason se)) /\
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret_ty (Assert e (AssertReason se))) /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assert e (AssertReason se)) es = (res, es') /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
             (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type se) se es1) /\
    ~reason_covered cenv se ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se))) es res es'
Proof
  cheat
QED

(* The reason simulates where the condition is false: both are pure, so
   the condition's evaluation keeps expr_sim_inv (expr_sim_pre_eval). *)
Theorem assert_reason_vv_sim[local]:
  !cx e se tops ctx func cenv env es es1.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ok cx se) /\
    body_inv tops ctx cenv cx /\ expr_sim_pre cenv cx env e es /\
    well_typed_expr env se /\ int_calls_expr se = [] /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) se /\
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
    (gvs[expr_body_pre_def, expr_sim_pre_def] >>
     CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
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
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
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
  `!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
           (INL (BoolV F), es1) ==>
         expr_vv_sim ctx func cenv cx (expr_type se) se es1` by
    (rpt strip_tac >> irule assert_reason_vv_sim >>
     gvs[expr_sim_pre_body, stmt_exprs_ok_def,
         supported_stmt_expr_exists_def, supported_assert_exists_def] >>
     metis_tac[]) >>
  Cases_on `reason_covered cenv se`
  >- (gvs[reason_covered_def]
      >- (irule compile_assert_reason_frag >> simp[] >> metis_tac[])
      >- (irule compile_assert_storage_reason_frag >> simp[] >>
          metis_tac[])) >>
  irule body_assert_reason_other >> simp[] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* GAP (#637 log): no statement lemma for Log yet.  body_inv ties
   ce_event_info to the program's events, and supported_log the
   arguments' types to the event's fields. *)
Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  cheat
QED

(* GAP (#637 declarations): stmtSimDecl's compile_annassign_stmt_frag,
   compile_annassign_word_stmt_frag and compile_annassign_typed_stmt_frag,
   stmtSimDeclMem's compile_annassign_memory_stmt_frag and
   compile_annassign_memory_widen_stmt_frag, and stmtSimDeclEmpty's
   compile_annassign_empty_stmt_frag cover the value's forms, but all ask
   (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) of the
   declared name.  body_inv does not give it: that needs a clause on the
   compile env's variables and that id is a local's name (dot-free), which
   only supported_function_bindings gives, at the program level.  The
   memory forms also ask the memory local's size bounds, as for Assign. *)
Theorem body_annassign_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) ==>
    body_stmt_ok cx (AnnAssign id typ e)
Proof
  cheat
QED

(* GAP (#637 append): no statement lemma for Append yet; the target's
   pointer comes from compile_get_target_ptr. *)
Theorem body_append_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx t ==>
    body_stmt_ok cx (Append t e)
Proof
  cheat
QED

(* ===== Assignments ===== *)

(* expr_sim_pre_eval_result and expr_sim_pre_eval under expr_body_pre:
   their proofs never use int_calls_expr e = []. *)
Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es'
Proof
  rpt gen_tac >> simp[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `es'`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- gvs[] >> strip_tac >>
  `outcomes_accounts_typed es'.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  gvs[] >> first_assum ACCEPT_TAC
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

(* A word type takes no wider type (type_widens_to). *)
Theorem type_widens_to_word:
  !tenv t u. type_widens_to tenv t u /\ is_word_type u ==> t = u
Proof
  rw[type_widens_to_def] >>
  Cases_on `t` >> Cases_on `u` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> Cases_on `d2` >> gvs[arg_type_fits_def, is_word_type_def]
QED

(* An assignment to a word local: stmtSimAssign's
   compile_assign_local_stmt_frag. *)
Theorem body_assign_local_word[local]:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
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
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `es1`, `id`, `expr_type e`] mp_tac
    expr_sim_inv_local >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[store_lays_out_typed]
QED

(* RESIDUAL (#637 assignments): the other base targets.
   - A local in memory: stmtSimAssignMem's
     compile_assign_local_memory_stmt_frag asks of the local's type
     type_memory_bytes cenv vtyp = type_memory_size tyv,
     0 < type_memory_size tyv and type_memory_size tyv + 64 < dimword (:256),
     which nothing in body_stmt_ok gives, and expr_type e = vtyp and
     lowered_value_type cenv e = vtyp, where the typing lets e widen
     (type_widens_to); an empty value assigned to a type with a length
     word (has_length_word, is_empty_value_expr) has no lemma.
   - A storage variable: stmtSimAssignStorage's
     compile_assign_storage_typed_stmt_frag asks
     cenv.ce_hashmap_info (module_var_key (src, id)) = NONE and
     cenv.ce_var_type (module_var_key (src, id)) = SOME vtyp, which body_inv
     does not give (it fixes no module variable metadata of cenv).
   - Subscript and attribute targets: no statement lemma (the simulation
     of compile_get_target_ptr on eval_target_place). *)
Theorem body_assign_other:
  !cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (Assign (BaseTarget t) e) es = (res, es') /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e)) es res es'
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
  Cases_on `?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
                    is_word_type ty`
  >- (gvs[] >> irule body_assign_local_word >> metis_tac[]) >>
  irule body_assign_other >> metis_tac[]
QED

(* The i-th local of a tuple of word locals takes the i-th value as
   stored. *)
Theorem tuple_local_lays_out[local]:
  !cenv cx env es1 ids tys tvs vs i entry.
    expr_sim_inv cenv cx env es1 /\
    (!j. j < LENGTH ids ==>
         FLOOKUP env.var_types (EL j ids) = SOME (EL j tys)) /\
    LENGTH tys = LENGTH ids /\ EVERY is_word_type tys /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    LIST_REL value_has_type tvs vs /\
    i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
    store_lays_out (EL i tvs) entry.type (EL i vs)
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\ is_word_type (EL i tys)` by
    gvs[LIST_REL_EL_EQN, EVERY_EL] >>
  `FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by simp[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[store_lays_out_typed]
QED

(* A tuple of word locals: stmtSimAssignTuple's
   compile_assign_tuple_locals_stmt_frag. *)
Theorem body_assign_tuple_locals[local]:
  !cx ids e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (res, es') /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\ is_word_type ty)
      ids ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      es res es'
Proof
  rpt strip_tac >>
  `EVERY (\id. ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
                         cenv.ce_var_type id = SOME vt /\ is_word_type vt)
     ids` by
    (gvs[EVERY_MEM] >> rw[] >> rename1 `MEM x ids` >>
     qpat_x_assum `!x. MEM x ids ==> _` drule >> strip_tac >>
     rename1 `FLOOKUP env.var_types x = SOME ty` >>
     drule_all expr_sim_inv_local >> strip_tac >>
     `cenv.ce_var_type x = SOME ty` by fs[expr_sim_inv_def] >> simp[]) >>
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
  `EVERY is_word_type tys` by
    (rw[EVERY_EL] >> gvs[EVERY_EL] >> metis_tac[optionTheory.SOME_11]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim ctx func cenv cx (TupleT tys) e es` by
    metis_tac[body_expr_ok_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def,
       optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
           (INL v, es1) ==> value_has_type (TupleTV tvs) v` by
    (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
     gvs[value_runtime_typed_def]) >>
  `!vs es1 i entry.
     (do result <- eval_expr cx e; read_result cx result od) es =
       (INL (ArrayV (TupleV vs)), es1) /\
     i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
     store_lays_out (EL i tvs) entry.type (EL i vs)` by
    (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
     gvs[value_runtime_typed_def, value_has_type_def,
         values_have_types_LIST_REL] >>
     drule_all tuple_local_lays_out >> simp[]) >>
  irule compile_assign_tuple_locals_stmt_frag >> simp[] >>
  qexistsl_tac [`tys`, `TupleTV tvs`] >> simp[]
QED

(* RESIDUAL (#637 tuple assignments): the other tuple targets.
   - Locals in memory: stmtSimAssignTupleMem's
     compile_assign_tuple_locals_memory_stmt_frag asks cenv.ce_target
     CapMcopy, type_memory_size (TupleTV tvs) < dimword (:256) and, for each
     memory local, 0 < type_memory_size vtv and
     type_memory_size vtv + 64 < dimword (:256), which nothing in
     body_stmt_ok gives.
   - Storage, subscript and attribute elements: no statement lemma for
     compile_tuple_store_all.
   An empty tuple target is supported but has no lemma either.  A nested
   TupleTarget is not supported (supported_assignment). *)
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
    eval_stmt cx (Assign (TupleTarget gs) e) es = (res, es') /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                             is_word_type ty) ids) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e)) es res es'
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
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                                   is_word_type ty) ids`
  >- (gvs[] >> irule body_assign_tuple_locals >> metis_tac[]) >>
  irule body_assign_tuple_other >> metis_tac[]
QED

(* ===== Augmented assignments ===== *)

(* x op= e on a local, e with no internal call: stmtSimAugAssign's
   compile_augassign_local_stmt_frag. *)
Theorem body_augassign_local[local]:
  !cx ty id bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) /\
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    int_calls_expr e = [] ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      es res es'
Proof
  rpt strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def,
         int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_augassign_local_stmt_frag >>
  gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
      AllCaseEqs(), expr_sim_pre_body] >>
  metis_tac[compile_expr_sim_mutual, expr_ok_def]
QED

(* RESIDUAL (#637 augmented assignment): the other targets, and a local
   whose operand makes an internal call.  compile_augassign_local_stmt_frag
   asks expr_sim_ok and expr_sim_pre of the operand (its x op e goes
   through compile_bop_word_sim under expr_sim_pre), which an operand with
   an internal call does not meet; storage, subscript and attribute
   targets have no statement lemma. *)
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
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AugAssign ty t bop e) es = (res, es') /\
    ~((?id. t = NameTarget id) /\ int_calls_expr e = []) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e)) es res es'
Proof
  cheat
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
  Cases_on `(?id. t = NameTarget id) /\ int_calls_expr e = []`
  >- (gvs[] >> irule body_augassign_local >> metis_tac[]) >>
  irule body_augassign_other >> metis_tac[]
QED

(* GAP (#637 if): stmtSimIf's compile_if_stmt_frag, given the
   branches' judgments at the pushed scope.  Left: cs_mono of stmts_env
   (no lemma that compile_stmt only appends yet), and the branches'
   premises at the pushed scope (expr_sim_inv, the typing). *)
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
  cheat
QED

(* GAP (#637 for): stmtSimFor's compile_for_range_frag and
   compile_for_range_lit_frag and stmtSimForRange's
   compile_for_range_checked_frag cover ranges.  Their premises not given
   by body_stmt_ok and the IHs:
   - (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) for
     the loop variable (as for AnnAssign);
   - bound < dimword (:256);
   - compile_stmts of the body growing the compile state for every start
     state (!c lc sa sb); loweringShapeProps' compile_stmt_shape gives it
     only under its own conditions;
   - the body's premises at each iteration's scope (expr_sim_inv kept
     through eval_stmts);
   - the checked lemma's bound on the counter for an empty range, and the
     choice between the literal and the checked lemma, which turns on
     whether both ends lower to Lit, not on their syntax.
   Iteration over an array has no lemma. *)
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
  cheat
QED

(* GAP (#637 expression statements): stmtSim's compile_expr_stmt_frag,
   given the expression's expr_vv_sim (the IH) and that compile_expr
   leaves its block open, which has no lemma yet. *)
Theorem body_expr_stmt_case:
  !cx e. body_expr_ok cx e ==> body_stmt_ok cx (Expr e)
Proof
  cheat
QED

(* ===== Statement lists ===== *)

Theorem body_stmts_nil_case:
  !cx. body_stmts_ok cx []
Proof
  rw[body_stmts_ok_def] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> rw[stmt_frag_nil]
QED

(* GAP (#637 statement lists): stmtSim's stmt_frag_cons, given
   cs_mono of compile_stmt and stmts_env (no lemma yet), the head's
   judgment (the IH), and the tail's at every c with
   cenv_top_ext cenv c es1.scopes.  Left: those, and the tail's premises
   at es1: expr_sim_inv at the env the head's typing gives, and at c.
   stmt_frag_cons asks for the tail at every such c, while the
   declarations bind only the c that stmt_env returns; a variant of
   stmt_frag_cons for that c may be needed. *)
Theorem body_stmts_cons_case:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ok cx ss) /\
    body_stmt_ok cx s ==>
    body_stmts_ok cx (s::ss)
Proof
  cheat
QED
