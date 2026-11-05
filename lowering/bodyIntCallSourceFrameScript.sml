(* Source effects admitted by supported internal-call arguments. *)
Theory bodyIntCallSourceFrame
Ancestors
  supportedExprs supportedExprForms vyperPureExpr vyperInterpreter vyperState
  vyperStatePreservation vyperPlaceFrames loweringPosts exprSimHyps exprSimHypsDefs exprSimSource

Theorem outcomes_frame_trans[local]:
  s1 = s0 with <| outcomes := s1.outcomes; gas_obs := s1.gas_obs |> /\
  s2 = s1 with <| outcomes := s2.outcomes; gas_obs := s2.gas_obs |> ==>
  s2 = s0 with <| outcomes := s2.outcomes; gas_obs := s2.gas_obs |>
Proof
  simp[evaluation_state_component_equality] >> metis_tac[]
QED

Theorem outcomes_frame_bind[local]:
  (!s r t. f s = (r,t) ==> t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  (!x s r t. g x s = (r,t) ==> t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  bind f g s = (r,t) ==>
  t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[outcomes_frame_trans]
QED

Theorem outcomes_frame_precompile[local]:
  precompile_call_success bt s = (r,t) ==>
  t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>
Proof
  strip_tac >> drule precompile_call_success_state >>
  strip_tac >> gvs[evaluation_state_component_equality]
QED

Theorem supported_builtin_not_len[local]:
  supported_builtin_form tops ty blt es ==>
  blt <> Len
Proof
  Cases_on `blt` >> simp[supported_builtin_form_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `es` >> gvs[]
QED

Theorem supported_eval_outcomes_frame:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  (!tops es. supported_pure_exprs tops es ==>
    !cx s r t. eval_exprs cx es s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r t. eval_exprs cx (MAP SND fields) s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >>~- ([`eval_expr _ (Name _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (Literal _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (TopLevelName _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_exprs _ [] _ = _`], gvs[Once evaluate_def, return_def])
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
        type_check_def, assert_def, return_def, raise_def] >>
    imp_res_tac lift_sum_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (StructLit _ _ _) _ = _`],
    rename1 `StructLit ty id fields` >> PairCases_on `id` >>
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    imp_res_tac lift_sum_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> imp_res_tac select_result_state >>
    gvs[] >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (IfExp _ _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, raise_def] >>
    imp_res_tac read_result_state >>
    imp_res_tac conditional_result_state >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
    metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (Builtin _ _ _) _ = _`],
    drule supported_builtin_not_len >> strip_tac >>
    Cases_on `blt = Env MsgGas`
    >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
            return_def, raise_def, next_gas_reading_def, AllCaseEqs(),
            evaluation_state_component_equality]) >>
    gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
        type_check_def, assert_def, return_def, raise_def, get_accounts_def] >>
    imp_res_tac lift_sum_state >> gvs[] >>
    imp_res_tac outcomes_frame_precompile >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_exprs _ (_::_) _ = _`],
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> gvs[] >> metis_tac[outcomes_frame_trans])
QED


Theorem supported_eval_expr_outcomes:
  supported_pure_expr tops e /\ eval_expr cx e s = (r,t) ==>
  t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>
Proof
  metis_tac[CONJUNCT1 supported_eval_outcomes_frame]
QED

Theorem supported_eval_expr_results_outcomes:
  !args s r t.
    EVERY (supported_pure_expr tops) args /\
    eval_expr_results cx args s = (r,t) ==>
    t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>
Proof
  Induct_on `args` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  metis_tac[supported_eval_expr_outcomes, outcomes_frame_trans]
QED

Theorem get_storage_outcomes[local]:
  vyperStorageBackend$get_storage cx (es with outcomes := os) tr =
  get_storage cx es tr
Proof
  Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem read_place_outcomes:
  read_place cx p (es with outcomes := os) =
    (FST (read_place cx p es), es with outcomes := os)
Proof
  Cases_on `p` >>
  simp[read_place_def, vyperStorageBackendTheory.read_storage_slot_eq,
       get_storage_outcomes, get_scopes_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem read_result_outcomes:
  read_result cx raw (es with outcomes := os) =
    (FST (read_result cx raw es), es with outcomes := os)
Proof
  Cases_on `raw` >>
  simp[read_result_def, read_place_outcomes, return_def, raise_def] >>
  metis_tac[read_place_state, pairTheory.PAIR]
QED

Theorem read_result_outcomes_iff:
  read_result cx raw (es with outcomes := os) =
    (res, es with outcomes := os) <=> read_result cx raw es = (res,es)
Proof
  simp[read_result_outcomes] >>
  Cases_on `read_result cx raw es` >>
  drule read_result_state >> simp[]
QED

Theorem read_results_outcomes:
  !raw es os. read_results cx raw (es with outcomes := os) =
    (FST (read_results cx raw es), es with outcomes := os)
Proof
  Induct_on `raw` >> simp[read_results_def, return_def] >>
  rpt gen_tac >>
  simp[bind_def, read_result_outcomes] >>
  Cases_on `read_result cx h es` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> simp[] >>
  Cases_on `read_results cx raw es` >>
  drule read_results_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> simp[return_def]
QED

Theorem read_results_outcomes_iff:
  read_results cx raw (es with outcomes := os) =
    (res, es with outcomes := os) <=> read_results cx raw es = (res,es)
Proof
  simp[read_results_outcomes] >>
  Cases_on `read_results cx raw es` >>
  drule read_results_state >> simp[]
QED

Theorem storage_holds_outcomes:
  storage_holds cx tr t tv w (es with outcomes := os) s <=>
  storage_holds cx tr t tv w es s
Proof
  simp[storage_holds_def, read_result_outcomes_iff,
       vyperStorageBackendTheory.read_storage_slot_eq, get_storage_outcomes,
       AllCaseEqs()]
QED

Theorem immutable_holds_outcomes:
  immutable_holds cenv cx t tv w (es with outcomes := os) s <=>
  immutable_holds cenv cx t tv w es s
Proof
  simp[immutable_holds_def, read_result_outcomes_iff]
QED

Theorem vv_holds_outcomes:
  vv_holds cenv cx t tv vv (es with outcomes := os) s <=>
  vv_holds cenv cx t tv vv es s
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, read_result_outcomes_iff] >>
  Cases_on `p.ptr_location` >>
  simp[storage_holds_outcomes, immutable_holds_outcomes]
QED

Theorem vv_at_outcomes:
  vv_at cenv cx t sa sb (es with outcomes := os) tv vv s <=>
  vv_at cenv cx t sa sb es tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_at_def, read_result_outcomes_iff, expr_val_at_def]
QED

Theorem expr_body_pre_next_argument:
  expr_body_pre cenv cx env e es /\
  eval_expr cx e es = (res,es') /\
  expr_body_pre cenv cx env a es ==>
  expr_body_pre cenv cx env a es'
Proof
  strip_tac >> drule_all expr_body_pre_eval_result >>
  strip_tac >> gvs[expr_body_pre_def]
QED

Theorem expr_body_pre_next_arguments:
  expr_body_pre cenv cx env e es /\
  eval_expr cx e es = (res,es') /\
  EVERY (\a. expr_body_pre cenv cx env a es) args ==>
  EVERY (\a. expr_body_pre cenv cx env a es') args
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[expr_body_pre_next_argument]
QED
