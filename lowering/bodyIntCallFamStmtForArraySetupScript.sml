(* Source preparation for the counted Array producer. *)
Theory bodyIntCallFamStmtForArraySetup
Ancestors
  bodyIntCallFamStmtForArrayProducer stmtSimForArray bodySim
  exprSimHypsDefs vyperTyping vyperTypeSystem vyperTypeInvariants
  vyperInterpreter vyperState vyperValue vyperArray finite_map list

Theorem intcall_array_source_inputs:
  supported_stmt tops bindings (For id fty (Array arr) bound stmts) /\
  type_stmt env ret_ty (For id fty (Array arr) bound stmts) = SOME env' /\
  expr_sim_inv ce cx env es /\ ce_locals_declared ce env ==>
  ?name env_b snapshot tv ptr sz al vs.
    arr = Name (ArrayT fty (Fixed bound)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT fty (Fixed bound)) name) /\
    assignable_type env.type_defs fty /\ id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT fty (Fixed bound)) name)) stmts /\
    type_stmts (extend_local env id fty F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME snapshot /\
    evaluate_type (get_tenv cx) fty = SOME tv /\
    snapshot.type = ArrayTV tv (Fixed bound) /\
    value_has_type snapshot.type snapshot.value /\
    well_formed_type_value snapshot.type /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    ce.ce_var_type name = SOME (ArrayT fty (Fixed bound)) /\
    0 < bound /\ bound < dimword (:256) /\
    snapshot.value = ArrayV (SArrayV al) /\
    vs = array_elements (ArrayTV tv (Fixed bound)) (SArrayV al) /\
    LENGTH vs = bound /\
    (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
    (!gs. eval_iterator cx (Array arr) (es with gas_obs := gs) =
      (INL vs, es with gas_obs := gs)) /\
    FLOOKUP ce.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule_all array_for_hypotheses >> strip_tac >> gvs[] >>
  drule_all array_name_local_binding >> strip_tac >>
  `?al. entry.value = ArrayV (SArrayV al)` by
    (qpat_x_assum `value_has_type entry.type entry.value` mp_tac >>
     simp[] >> Cases_on `entry.value` >> simp[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >>
     Cases_on `av` >> simp[value_has_type_def]) >>
  rename1 `entry.value = ArrayV (SArrayV al)` >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var arrptr) arrsz)` >>
  `evaluate_type (get_tenv cx) (ArrayT fty (Fixed bound)) = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
        well_typed_expr_def] >> metis_tac[]) >>
  qexistsl [`entry`, `elem_tv`, `arrptr`, `arrsz`, `al`] >> simp[] >>
  simp[fixed_array_elements_length] >>
  conj_tac >-
    (gen_tac >> disch_tac >> fs[] >>
     metis_tac[fixed_array_elements_typed]) >>
  conj_tac >-
    (gen_tac >> irule eval_iterator_fixed_name >>
     simp[] >> metis_tac[]) >>
  conj_tac >-
    (fs[ce_locals_declared_def] >>
     Cases_on `FLOOKUP ce.ce_vars id` >> metis_tac[]) >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
     FLOOKUP_DEF] >>
  Cases_on `lookup_scopes id es.scopes` >> gvs[] >> metis_tac[]
QED

(* Pure iterator preparation emits no source gas events. *)
Theorem intcall_array_eval_for_source:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs = n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) ==>
  !gs. eval_stmt cx (For id et it n stmts) (es with gas_obs := gs) =
    eval_for cx tv id stmts vs (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def, lift_option_type_def, bind_def, return_def,
       ignore_bind_def, check_def, compatible_bound_def, assert_def]
QED

Theorem intcall_array_for_admissible:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs = n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) /\
  gas_admissible (eval_stmt cx (For id et it n stmts)) ok es ==>
  gas_admissible (eval_for cx tv id stmts vs) ok es
Proof
  strip_tac >> drule_all intcall_array_eval_for_source >>
  strip_tac >> fs[gasContextTheory.gas_admissible_def] >> metis_tac[]
QED
