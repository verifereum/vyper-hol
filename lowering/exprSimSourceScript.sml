(* Source preconditions and invariant preservation for expression evaluation. *)
Theory exprSimSource
Ancestors
  exprSimHypsDefs exprSimDefs loweringSlice allocLimits gasContext list finite_map pair
  vyperTyping
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperTypeExprResult vyperTypeEvalSoundness vyperTypeBuiltins
  vyperExprNoControl vyperEvalOutcomeSuffix vyperRuntimeAccounts
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperCallOutcomeStorage
  supportedExprTraverse exprStoragePreservation
  vyperLookup vyperPlaceResultTyping supportedProgram bodyStoragePreservation
  vyperTypeABI vyperValue vyperPlaceInvariants placeTypingProps
Libs
  pairLib monadsyntax

Theorem expr_sim_pre_gas_obs[simp]:
  expr_sim_pre cenv cx env e (es with gas_obs := gs) <=>
  expr_sim_pre cenv cx env e es
Proof
  simp[expr_sim_pre_def]
QED

Theorem expr_body_pre_gas_obs[simp]:
  expr_body_pre cenv cx env e (es with gas_obs := gs) <=>
  expr_body_pre cenv cx env e es
Proof
  simp[expr_body_pre_def]
QED

Theorem expr_sim_pre_body:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es <=>
    expr_body_pre cenv cx env e es /\ int_calls_expr e = []
Proof
  rw[expr_sim_pre_def, expr_body_pre_def, EQ_IMP_THM] >> gvs[]
QED

Theorem expr_sim_pre_body_pre:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es ==> expr_body_pre cenv cx env e es
Proof
  simp[expr_sim_pre_body]
QED



(* The induction predicate: both judgments, so a case can use whichever an
   operand's lowering needs. *)



Theorem expr_body_pre_storage_preserved:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    contract_storage_well_formed cx es' /\ oracle_storage_ok cx es'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `int_calls_expr e = []`
      >- (irule eval_expr_oracle_preserves_contract_storage_well_formed >>
          gvs[expr_body_pre_def, expr_sim_inv_def,
              runtime_storage_consistent_def, runtime_consistent_def] >>
          metis_tac[]) >>
      `?tops. supported_program tops /\ get_module_code cx NONE = SOME tops`
        by (Cases_on `int_calls_expr e` >> gvs[expr_body_pre_def] >>
            metis_tac[]) >>
      irule eval_expr_body_oracle_storage >>
      gvs[expr_body_pre_def, expr_sim_inv_def, listTheory.EVERY_CONJ,
          runtime_storage_consistent_def, runtime_consistent_def] >>
      metis_tac[]) >>
  irule oracle_storage_ok_suffix >> qexists_tac `es` >>
  gvs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_then irule (cj 5 eval_outcome_suffix_mutual)
QED

(* The outcomes stay SOME: evaluation only drops some from the front. *)
Theorem eval_expr_outcomes_some:
  !cx e es res es'.
    IS_SOME es.outcomes /\ eval_expr cx e es = (res, es') ==>
    IS_SOME es'.outcomes
Proof
  rpt strip_tac >> drule (cj 5 eval_outcome_suffix_mutual) >>
  rw[outcome_suffix_def] >> gvs[]
QED

Theorem replace_popped_keys[local]:
  !h tv path r h'.
    replace_popped tv path r h = SOME h' ==> MAP FST h' = MAP FST h
Proof
  Induct >> simp[replace_popped_def] >> Cases >> rpt gen_tac >>
  simp[replace_popped_def] >> rw[AllCaseEqs()] >> gvs[] >> res_tac
QED

Theorem replace_popped_history_typed[local]:
  !h tv path ptv v h'.
    popped_history_typed tv h /\ well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv /\ value_has_type ptv v /\
    replace_popped tv path v h = SOME h' ==>
    popped_history_typed tv h'
Proof
  Induct >> simp[replace_popped_def] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >>
  simp[popped_history_typed_cons] >> rpt strip_tac >>
  gvs[Once replace_popped_def, AllCaseEqs()] >>
  simp[popped_history_typed_cons]
  >- (irule vyperPlaceStatePreservationTheory.assign_subscripts_replace_type_metadata >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `IS_PREFIX path head0` mp_tac >>
      simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
      gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
      metis_tac[subscripts_type_append]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem entry_pop_step_event_valid[local]:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  popped_history_typed entry.type entry.popped /\
  entry_pop_step entry path next ==>
  entry_pop_event_valid (entry,path)
Proof
  rpt strip_tac >>
  `?arr p. read_memory_path entry path = INL arr /\
           popped_value arr = INL p` by
    metis_tac[entry_pop_step_def] >>
  qpat_x_assum `entry_pop_step _ _ _` kall_tac >>
  `?ptv. subscripts_type entry.type path = SOME ptv /\
         value_has_type ptv arr` by
    (qpat_x_assum `read_memory_path _ _ = _` mp_tac >>
     simp[read_memory_path_def, AllCaseEqs()] >> strip_tac
     >- metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists] >>
     metis_tac[read_popped_declared_type_exists,
               vyperPlaceStatePreservationTheory.read_popped_type]) >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  rename1 `popped_value (ArrayV av) = INL p` >>
  Cases_on `av` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `ptv` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv bound) (ArrayV (DynArrayV xs))` >>
  Cases_on `bound` >> gvs[vyperTypingTheory.value_has_type_def] >>
  simp[entry_pop_event_valid_def, vyperTypingTheory.value_has_type_def]
QED

Theorem entry_pop_step_keys_indexed[local]:
  entry_pop_step entry path next /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  popped_history_typed entry.type entry.popped /\
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
    subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST entry.popped) ==>
  popped_history_typed next.type next.popped /\
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
    subscripts_type next.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST next.popped)
Proof
  strip_tac >>
  `entry_pop_event_valid (entry,path)` by
    (drule_all entry_pop_step_event_valid >> simp[]) >>
  gvs[entry_pop_event_valid_def] >>
  `well_formed_type_value etv` by
    (drule_all vyperPlaceStatePreservationTheory.subscripts_type_well_formed >>
     simp[vyperTypingTheory.well_formed_type_value_def]) >>
  qpat_x_assum `entry_pop_step _ _ _` mp_tac >>
  simp[entry_pop_step_def] >> strip_tac >> gvs[]
  >- (conj_tac
      >- (irule vyperPlaceStatePreservationTheory.record_pop_history_typed_at_path >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      Cases_on `arr` >> gvs[record_pop_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[record_pop_def] >>
      metis_tac[]) >>
  `value_has_type (ArrayTV etv (Dynamic n)) shortened` by
    metis_tac[vyperAssignPreservesTypeTheory.pop_element_preserves_type] >>
  `popped_history_typed entry.type history` by
    (irule replace_popped_history_typed >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `MAP FST history = MAP FST entry.popped` by metis_tac[replace_popped_keys] >>
  conj_tac
  >- (irule vyperPlaceStatePreservationTheory.record_pop_history_typed_at_path >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `arr` >> gvs[record_pop_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[record_pop_def] >>
  metis_tac[]
QED

Theorem scope_pop_step_keys_indexed[local]:
  !sc ev sc'.
    scope_pop_step sc ev sc' /\ EVERY scope_well_typed sc /\
    popped_keys_indexed sc ==>
    EVERY scope_well_typed sc' /\ popped_keys_indexed sc'
Proof
  rpt gen_tac >> PairCases_on `ev` >>
  simp[scope_pop_step_def] >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  gvs[popped_keys_indexed_def, scope_well_typed_def] >>
  `value_has_type ev1.type ev1.value /\ well_formed_type_value ev1.type` by
    metis_tac[] >>
  `popped_history_typed ev1.type ev1.popped` by metis_tac[] >>
  `entry_pop_event_valid (ev1,ev2)` by
    (drule_all entry_pop_step_event_valid >> simp[]) >>
  `value_has_type next.type next.value` by
    (drule_all vyperPlaceMutationSoundnessTheory.entry_pop_step_value_type >> simp[]) >>
  drule entry_pop_step_metadata >> strip_tac >>
  drule entry_pop_step_keys_indexed >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rw[FLOOKUP_UPDATE] >> gvs[] >> metis_tac[]
QED

Theorem scope_pop_trace_keys_indexed:
  !events sc sc'.
    scope_pop_trace sc events sc' /\ EVERY scope_well_typed sc /\
    popped_keys_indexed sc ==>
    EVERY scope_well_typed sc' /\ popped_keys_indexed sc'
Proof
  Induct >> simp[scope_pop_trace_def] >> rpt strip_tac >>
  drule_all scope_pop_step_keys_indexed >> strip_tac >>
  first_x_assum drule >> simp[]
QED


(* Evaluating an expression changes the scopes only by pops
   (eval_mutual_scope_pop_effect).  A pop from a well-typed local, whose
   history is typed, removes the element of a dynamic array, records it at
   its index and keeps the local and its history typed. *)
Theorem eval_expr_popped_keys_indexed:
  !cx e es res es'.
    eval_expr cx e es = (res, es') /\ state_well_typed es /\
    popped_keys_indexed es.scopes ==>
    popped_keys_indexed es'.scopes
Proof
  rpt strip_tac >>
  `scope_pop_effect (eval_expr cx e)` by
    simp[cj 5 eval_mutual_scope_pop_effect] >>
  gvs[scope_pop_effect_def] >> first_x_assum drule >> strip_tac >>
  gvs[state_well_typed_def] >>
  drule_all scope_pop_trace_keys_indexed >> simp[]
QED

Theorem expr_body_pre_eval_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==>
         eval_result_typed (env,cx,es') tv (Type (expr_type e))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_storage_preserved >> strip_tac >>
  `IS_SOME es'.outcomes` by
    (irule eval_expr_outcomes_some >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `es'`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- gvs[] >>
  `outcomes_accounts_typed es'.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  Cases_on `res` >> gvs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem expr_sim_pre_eval_result:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==>
         eval_result_typed (env,cx,es') tv (Type (expr_type e))
Proof
  metis_tac[expr_body_pre_eval_result, expr_sim_pre_body_pre]
QED

Theorem expr_body_pre_eval:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !v. res = INL v ==> expr_result_typed env e (Value v)
Proof
  rpt strip_tac >>
  `state_well_typed es' /\ no_type_error_result res /\
   (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)` by
    (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >> simp[] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
      value_result_typed_def, is_HashMapRef_def]
QED

Theorem expr_sim_pre_eval:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !v. res = INL v ==> expr_result_typed env e (Value v)
Proof
  metis_tac[expr_body_pre_eval, expr_sim_pre_body_pre]
QED


Theorem eval_expr_read_INL:
  !cx e es v es'.
    (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es') ==>
    ?tv t. eval_expr cx e es = (INL tv, t) /\ read_result cx tv t = (INL v, es')
Proof
  simp[bind_def, AllCaseEqs()] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "EXPRESSION_SOURCE_AUDIT OK\n"
     else raise Fail "expression source preservation inherited admission"
  end) [expr_sim_pre_gas_obs,
        expr_body_pre_gas_obs,
        expr_sim_pre_body,
        expr_sim_pre_body_pre,
        expr_body_pre_storage_preserved,
        eval_expr_outcomes_some,
        scope_pop_trace_keys_indexed,
        eval_expr_popped_keys_indexed,
        expr_body_pre_eval_result,
        expr_sim_pre_eval_result,
        expr_body_pre_eval,
        expr_sim_pre_eval,
        eval_expr_read_INL];

Theorem expr_body_pre_res_ok:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_res_ok res
Proof
  rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  Cases_on `res` >> gvs[expr_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  Cases_on `exc` >> gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem word_value_type_typed:
  !t tenv tyv x.
    word_value_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv x ==>
    word_value x /\ value_has_type tyv x
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `x` >>
  gvs[vyperTypingTheory.value_has_type_def, word_value_def]
QED

Theorem expr_body_pre_word_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ word_value_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
    !tv. res = INL tv ==>
         ?tyv. word_value tv /\
                 evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `res` >> gvs[]
  >- (gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
      drule_all word_value_type_typed >> strip_tac >> gvs[expr_res_ok_def]) >>
  irule expr_body_pre_res_ok >> simp[] >> metis_tac[]
QED

Theorem byte_widths_exprs_mem:
  !args e. byte_widths_exprs args /\ MEM e args ==> byte_widths_expr e
Proof
  Induct >> rw[byte_widths_expr_def] >> gvs[]
QED

Theorem alloc_limits_exprs_mem:
  !cenv args e. alloc_limits_exprs cenv args /\ MEM e args ==>
               alloc_limits_expr cenv e
Proof
  gen_tac >> Induct >> rw[alloc_limits_expr_def] >> gvs[]
QED

Theorem well_typed_exprs_member:
  !args env e. well_typed_exprs env args /\ MEM e args ==> well_typed_expr env e
Proof
  Induct >> rw[well_typed_expr_def] >> metis_tac[]
QED

Theorem call_evaluation_safe_exprs_mem:
  !args cx e.
    call_evaluation_safe cx (int_calls_exprs args) /\ MEM e args ==>
    call_evaluation_safe cx (int_calls_expr e)
Proof
  Induct >> rw[int_calls_expr_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
QED

Theorem int_calls_exprs_every_mem:
  !args e P. EVERY P (int_calls_exprs args) /\ MEM e args ==>
             EVERY P (int_calls_expr e)
Proof
  Induct >> rw[int_calls_expr_def] >> gvs[]
QED

Theorem expr_body_pre_builtin_arg:
  !cenv cx env ann bi args e es es'.
    expr_body_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "EXPRESSION_OPERAND_SOURCE_AUDIT OK\n"
     else raise Fail "operand source fact inherited admission"
  end) [expr_body_pre_res_ok,
        word_value_type_typed,
        expr_body_pre_word_result,
        byte_widths_exprs_mem,
        alloc_limits_exprs_mem,
        well_typed_exprs_member,
        call_evaluation_safe_exprs_mem,
        int_calls_exprs_every_mem,
        expr_body_pre_builtin_arg];
