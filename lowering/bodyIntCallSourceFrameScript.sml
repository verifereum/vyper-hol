(* Source reads are insensitive to the outcome and gas oracle streams. *)
Theory bodyIntCallSourceFrame
Ancestors
  vyperInterpreter vyperState vyperStatePreservation vyperStorageBackend
  supportedExprTraverse exprSimHypsDefs vyperPureExpr vyperPlaceFrames vyperContext

Theorem get_storage_outcomes[local]:
  vyperStorageBackend$get_storage cx (es with <|outcomes := os; gas_obs := gs|>) tr =
  get_storage cx es tr
Proof
  Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem read_place_outcomes:
  read_place cx p (es with <|outcomes := os; gas_obs := gs|>) =
    (FST (read_place cx p es), es with <|outcomes := os; gas_obs := gs|>)
Proof
  Cases_on `p` >>
  simp[read_place_def, vyperStorageBackendTheory.read_storage_slot_eq,
       get_storage_outcomes, get_scopes_def,
       get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem read_result_outcomes:
  read_result cx raw (es with <|outcomes := os; gas_obs := gs|>) =
    (FST (read_result cx raw es), es with <|outcomes := os; gas_obs := gs|>)
Proof
  Cases_on `raw` >>
  simp[read_result_def, read_place_outcomes, return_def, raise_def] >>
  metis_tac[read_place_state, pairTheory.PAIR]
QED

Theorem read_result_outcomes_iff:
  read_result cx raw (es with <|outcomes := os; gas_obs := gs|>) =
    (res, es with <|outcomes := os; gas_obs := gs|>) <=>
  read_result cx raw es = (res,es)
Proof
  simp[read_result_outcomes] >>
  Cases_on `read_result cx raw es` >>
  drule read_result_state >> simp[]
QED

Theorem read_results_outcomes:
  !raw es os gs. read_results cx raw (es with <|outcomes := os; gas_obs := gs|>) =
    (FST (read_results cx raw es), es with <|outcomes := os; gas_obs := gs|>)
Proof
  Induct_on `raw` >> simp[read_results_def, return_def] >>
  rpt gen_tac >> simp[bind_def, read_result_outcomes] >>
  rename1 `read_result cx head es` >>
  Cases_on `read_result cx head es` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `(head_res, es)` >>
  Cases_on `head_res` >> simp[] >>
  Cases_on `read_results cx raw es` >>
  drule read_results_state >> strip_tac >> gvs[] >>
  rename1 `(tail_res, es)` >>
  Cases_on `tail_res` >> simp[return_def]
QED

Theorem read_results_outcomes_iff:
  read_results cx raw (es with <|outcomes := os; gas_obs := gs|>) =
    (res, es with <|outcomes := os; gas_obs := gs|>) <=>
  read_results cx raw es = (res,es)
Proof
  simp[read_results_outcomes] >>
  Cases_on `read_results cx raw es` >>
  drule read_results_state >> simp[]
QED

Theorem outcomes_frame_trans[local]:
  s1 = s0 with <| outcomes := s1.outcomes; gas_obs := s1.gas_obs |> /\
  s2 = s1 with <| outcomes := s2.outcomes; gas_obs := s2.gas_obs |> ==>
  s2 = s0 with <| outcomes := s2.outcomes; gas_obs := s2.gas_obs |>
Proof
  simp[evaluation_state_component_equality] >> metis_tac[]
QED

Theorem eval_exprs_frame_from_members[local]:
  (!e. MEM e es ==> !s r t. eval_expr cx e s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) ==>
  !s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  Induct_on `es` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  `!s r t. eval_expr cx h s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>` by
    (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `!s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>` by
    (qpat_x_assum `_ ==> !s r t. eval_exprs _ _ _ = _ ==> _` match_mp_tac >>
     rpt strip_tac >>
     qpat_x_assum `!e. _` (qspec_then `e` mp_tac) >> simp[]) >>
  qpat_x_assum `!e. e = h \/ MEM e es ==> _` kall_tac >>
  qpat_x_assum `_ ==> !s r t. eval_exprs _ _ _ = _ ==> _` kall_tac >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[outcomes_frame_trans]
QED

Theorem outcomes_frame_precompile[local]:
  precompile_call_success bt s = (r,t) ==>
  t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>
Proof
  strip_tac >> drule precompile_call_success_state >>
  strip_tac >> gvs[evaluation_state_component_equality]
QED

Theorem outcomes_frame_exprs_members[local]:
  !es. (!e. MEM e es ==> !cx s r t. eval_expr cx e s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) ==>
  !cx s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  Induct >> simp[Once evaluate_def, return_def] >>
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[outcomes_frame_trans]
QED

Theorem eval_code_operand_state[local]:
  eval_exprs cx [addr] s = (r,t) ==>
  SND (eval_expr cx (Builtin ct (Acc Code) [addr]) s) = t
Proof
  strip_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, bind_def,
       ignore_bind_def, type_check_def, assert_def, return_def,
       get_accounts_def, lift_sum_def, raise_def] >>
  Cases_on `r` >> simp[] >>
  Cases_on `evaluate_builtin cx t.accounts ct (Acc Code) [expr_type addr] x` >>
  simp[return_def, raise_def]
QED

Theorem outcomes_frame_builtin_operands[local]:
  (!cx s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  (!e. MEM e es ==> !cx s r t. eval_expr cx e s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  (case code_slice_source bt es of
     NONE => eval_exprs cx es
   | SOME (ct,addr) => do
       tail_vs <- eval_exprs cx (TL es);
       addr_vs <- eval_exprs cx [addr];
       acc <- get_accounts;
       v <- lift_sum (evaluate_code_source cx acc (is_self_addr addr)
                       ct (expr_type addr) addr_vs);
       return (v::tail_vs)
     od) s = (r,t) ==>
  t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  strip_tac >>
  irule (BETA_RULE (Q.SPEC `\s t. t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>`
           builtin_operands_preserve)) >>
  conj_tac >- metis_tac[outcomes_frame_trans] >>
  qexistsl [`bt`, `cx`, `es`, `r`] >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule outcomes_frame_exprs_members >>
      gvs[code_slice_source_SOME] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >>
  drule eval_code_operand_state >> strip_tac >>
  gvs[code_slice_source_SOME] >>
  Cases_on `eval_expr cx (Builtin code_ty (Acc Code) [addr]) st` >>
  qpat_x_assum `!ct. SND _ = _` (qspec_then `code_ty` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem builtin_snapshot_frame[local]:
  (!s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  (!e. MEM e es ==> !s r t. eval_expr cx e s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  (!ct addr. code_slice_source bt es = SOME (ct,addr) ==>
    (!s r t. eval_exprs cx (TL es) s = (r,t) ==>
      t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
    (!s r t. eval_exprs cx [addr] s = (r,t) ==>
      t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>)) ==>
  !s r t. eval_expr cx (Builtin ty bt es) s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  rpt strip_tac >> Cases_on `bt = Len`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, AllCaseEqs()] >>
      strip_tac >> Cases_on `es` >> gvs[builtin_args_length_ok_def] >>
      imp_res_tac result_array_length_state >> gvs[] >> metis_tac[]) >>
  Cases_on `bt = Env MsgGas`
  >- (qpat_x_assum `!s r t. eval_exprs _ _ _ = _ ==> _` kall_tac >>
      qpat_x_assum `!e. MEM _ _ ==> _` kall_tac >>
      qpat_x_assum `!ct addr. code_slice_source _ _ = _ ==> _` kall_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, next_gas_reading_def,
           AllCaseEqs(), evaluation_state_component_equality] >>
      rpt strip_tac >> gvs[evaluation_state_component_equality]) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, lift_option_type_def] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      Cases_on `evaluate_type (get_tenv cx) (expr_type (EL 1 es))` >>
      gvs[raise_def, return_def] >>
      imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]) >>
  Cases_on `code_slice_source bt es`
  >- suspend "ordinary" >>
  PairCases_on `x` >> gvs[] >>
  suspend "snapshot"
QED

Resume builtin_snapshot_frame[ordinary]:
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac outcomes_frame_precompile >>
  metis_tac[outcomes_frame_trans]
QED

Resume builtin_snapshot_frame[snapshot]:
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac)) >>
  imp_res_tac outcomes_frame_precompile >>
  metis_tac[outcomes_frame_trans]
QED

Finalise builtin_snapshot_frame

(* HELD (train 17): 0.5.0b1 arg snapshot re-proof *)
Theorem outcomes_frame_builtin[local]:
  (!cx s r t. eval_exprs cx es s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  (!e. MEM e es ==> !cx s r t. eval_expr cx e s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>) /\
  eval_expr cx (Builtin ty bt es) s = (r,t) ==>
  t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  rpt strip_tac >> Cases_on `bt = Len`
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def] >>
      imp_res_tac result_array_length_state >> gvs[] >> metis_tac[]) >>
  Cases_on `bt = Env MsgGas`
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, next_gas_reading_def,
          AllCaseEqs(), evaluation_state_component_equality]) >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, lift_option_type_def] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      Cases_on `evaluate_type (get_tenv cx) (expr_type (EL 1 es))` >>
      gvs[raise_def, return_def] >>
      imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]) >>
  gvs[Once evaluate_def] >>
  qabbrev_tac `operands = (case code_slice_source bt es of
    NONE => eval_exprs cx es
  | SOME (ct,addr) => do
      tail_vs <- eval_exprs cx (TL es);
      addr_vs <- eval_exprs cx [addr];
      acc <- get_accounts;
      v <- lift_sum (evaluate_code_source cx acc (is_self_addr addr)
                      ct (expr_type addr) addr_vs);
      return (v::tail_vs)
    od)` >>
  `!s r t. operands s = (r,t) ==>
     t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>` by
    (unabbrev_all_tac >> rpt strip_tac >>
     irule outcomes_frame_builtin_operands >> metis_tac[]) >>
  gvs[bind_def, ignore_bind_def, type_check_def, assert_def, return_def,
      raise_def, get_accounts_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  imp_res_tac outcomes_frame_precompile >> metis_tac[outcomes_frame_trans]
QED

(* HELD (train 17): 0.5.0b1 arg snapshot re-proof *)
Theorem effect_free_eval_frame[local]:
  (!p e. !cx s r t. ~supported_expr_exists p e /\ p = expr_effect_root /\
    eval_expr cx e s = (r,t) ==>
    t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
  (!(p:expr -> bool) (target:base_assignment_target). T) /\
  (!p es. ~supported_exprs_exists p es /\ p = expr_effect_root ==>
    (!cx s r t. eval_exprs cx es s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>) /\
    (!e. MEM e es ==> !cx s r t. eval_expr cx e s = (r,t) ==>
      t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>)) /\
  (!(p:expr -> bool) (opt:expr option). T) /\
  (!p fields. !cx s r t. ~supported_fields_exists p fields /\ p = expr_effect_root /\
    eval_exprs cx (MAP SND fields) s = (r,t) ==>
    t = s with <| outcomes := t.outcomes; gas_obs := t.gas_obs |>)
Proof
  (* original proof, kept while held:
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def, expr_effect_root_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >>~- ([`eval_expr _ (Name _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (Literal _ _) _ = _`],
    gvs[Once evaluate_def, return_def])
  >>~- ([`eval_expr _ (TopLevelName _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (FlagMember _ _ _) _ = _`],
    gvs[Once evaluate_def] >> drule lookup_flag_mem_state >> strip_tac >> gvs[])
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
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> metis_tac[])
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> imp_res_tac select_result_state >>
    gvs[] >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (IfExp _ _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, raise_def] >>
    imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
    gvs[] >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
    metis_tac[outcomes_frame_trans])
  >>~- ([`eval_exprs _ (_::_) _ = _`],
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> gvs[] >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (Builtin _ _ _) _ = _`],
    irule outcomes_frame_builtin >> metis_tac[])
  >> gvs[expr_effect_root_def, listTheory.MEM] >> metis_tac[]
  *)
  cheat
QED

Theorem effect_free_eval_expr_outcomes:
  ~expr_has_effect e /\ eval_expr cx e s = (r,t) ==>
  t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  simp[expr_has_effect_def] >> metis_tac[CONJUNCT1 effect_free_eval_frame]
QED

Theorem effect_free_eval_exprs_outcomes:
  EVERY (\e. ~expr_has_effect e) es /\ eval_exprs cx es s = (r,t) ==>
  t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  pure_rewrite_tac[expr_has_effect_def, listTheory.EVERY_NOT_EXISTS] >>
  BETA_TAC >> pure_rewrite_tac[NOT_CLAUSES, ETA_THM] >>
  pure_rewrite_tac[GSYM supported_exprs_exists_every] >>
  metis_tac[CONJUNCT1 (CONJUNCT2 (CONJUNCT2 effect_free_eval_frame))]
QED

Theorem effect_free_eval_expr_results_outcomes:
  !args s r t.
    EVERY (\e. ~expr_has_effect e) args /\
    eval_expr_results cx args s = (r,t) ==>
    t = s with <|outcomes := t.outcomes; gas_obs := t.gas_obs|>
Proof
  Induct_on `args` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  metis_tac[effect_free_eval_expr_outcomes, outcomes_frame_trans]
QED

Theorem intcall_pre_effect_free_args:
  expr_body_pre cenv cx env (Call ann (IntCall id) args dflt) es ==>
  EVERY (\e. ~expr_has_effect e) args
Proof
  simp[expr_body_pre_def] >> rpt strip_tac >>
  drule (GEN_ALL (CONTRAPOS supported_expr_exists_root)) >>
  pure_rewrite_tac[call_operands_effect_root_def,
                   listTheory.EVERY_NOT_EXISTS] >>
  BETA_TAC >> pure_rewrite_tac[NOT_CLAUSES, ETA_THM] >> simp[]
QED

Theorem effect_free_results_read_result:
  EVERY (\e. ~expr_has_effect e) args /\
  eval_expr_results cx args s = (r,t) /\
  read_result cx raw s = (rv,s) ==>
  read_result cx raw t = (rv,t)
Proof
  strip_tac >> drule_all effect_free_eval_expr_results_outcomes >>
  strip_tac >> pop_assum SUBST1_TAC >> simp[read_result_outcomes_iff]
QED
