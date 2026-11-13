(* Tower-neutral source and memory facts for a local dynamic-array iterator. *)
Theory bodyDynArraySource
Ancestors
  bodySimDeclCases exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs
  list finite_map bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps
  stmtSimDecl stmtSimFor stmtSimForParts stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag vyperTyping fragExec compileEnv loweringStateRelDefs
  supportedStmts supportedStmtTraverse compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperAST vyperInterpreter vyperState vyperValue vyperValueOperation vyperTypeSystem
  vyperTypeInvariants vyperTypeValues targetPlaceSim exprSimTopLevelProps bodyStorageMetadata
  vyperTypeEnv memoryValueEncoding valueEncoding valueEncodingProps valueEncodingTyping exprSimAggregateEncoding
  venomState arithmetic
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem eval_iterator_dynamic_name:
  !cx ty c name es entry elem_tv vs.
    lookup_scopes name es.scopes = SOME entry /\
    entry.value = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) (ArrayT ty (Dynamic c)) =
      SOME (ArrayTV elem_tv (Dynamic c)) ==>
    eval_iterator cx (Array (Name (ArrayT ty (Dynamic c)) name)) es =
      (INL (MAP Value vs), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[array_iterator_results_def, read_result_def, read_place_def,
       read_memory_path_def, evaluate_subscripts_def, get_scopes_def,
       type_check_def, vyperStateTheory.assert_def, lift_option_type_def,
       lift_sum_def, ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, expr_type_def, extract_elements_def,
       array_elements_def]
QED

Theorem dynarray_elements_typed:
  value_has_type (ArrayTV tv (Dynamic c)) (ArrayV (DynArrayV vs)) /\
  well_formed_type_value (ArrayTV tv (Dynamic c)) /\ k < LENGTH vs ==>
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)
Proof
  strip_tac >>
  `value_has_type tv (EL k vs)` by
    fs[value_has_type_def, all_have_type_EVERY, EVERY_EL] >>
  metis_tac[value_has_type_val_wf]
QED

(* The local's alloca holds the length word, then the elements. *)
Theorem dynarray_snapshot_memory:
  !name ei entry tv c vs cenv dp sz ctx func cx s.
  lookup_scopes name ei.scopes = SOME entry /\
  entry.type = ArrayTV tv (Dynamic c) /\
  entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
  stmt_state_rel H ctx func cenv cx ei s ==>
  ?base. eval_operand (Var dp) s = SOME base /\
    mload (w2n base) s = n2w (LENGTH vs) /\
    (!k. k < LENGTH vs ==>
      val_in_memory tv (EL k vs)
        (w2n base + (k * type_memory_size tv + 32)) s.vs_memory /\
      w2n base + (k * type_memory_size tv + 32) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv ei.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `lookup_var dp s = SOME w0` >>
  qexists_tac `w0` >> simp[eval_operand_def] >>
  `val_in_memory (ArrayTV tv (Dynamic c)) (ArrayV (DynArrayV vs))
     (w2n w0) s.vs_memory` by metis_tac[memory_value_rel_val_in_memory] >>
  gvs[val_in_memory_dynarray, GSYM mem_word_at_eq_mload] >>
  rpt strip_tac
  >- (drule_all elems_in_memory_EL >> simp[]) >>
  `w2n w0 + (32 + c * type_memory_size tv) <= s.vs_alloca_next` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  `k <= c` by decide_tac >>
  `k * type_memory_size tv <= c * type_memory_size tv` by simp[] >>
  decide_tac
QED

Theorem dynarray_name_source_ready:
  c <= n /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty
    (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n stmts) = SOME env' ==>
  ?entry tv dp sz vs env_b.
    env' = env /\
    FLOOKUP env.var_types name = SOME (ArrayT typ (Dynamic c)) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ (Dynamic c)) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    lookup_scopes name es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    entry.type = ArrayTV tv (Dynamic c) /\
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c /\
    c < dimword (:256) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
    (!gs. eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name))
            (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >>
  `env' = env /\ FLOOKUP env.var_types name = SOME (ArrayT typ (Dynamic c)) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (Name (ArrayT typ (Dynamic c)) name)) stmts /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `?entry. lookup_scopes name es.scopes = SOME entry` by
    (gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
         optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Dynamic c)) = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `c < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def,
          bound_length_def] >> rpt strip_tac >>
     rename1 `0 < type_slot_size elem_tv` >>
     `c <= c * type_slot_size elem_tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `c * 1` >> simp[]) >>
     decide_tac) >>
  drule evaluate_type_ArrayT_cases >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  `?vs. entry.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c` by
    (Cases_on `entry.value` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  `?dp sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name))
          (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_dynamic_name >>
     conj_tac >- (qexists_tac `tv` >> gvs[]) >>
     qexists_tac `entry` >> simp[]) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  qexistsl_tac [`entry`, `tv`, `dp`, `sz`, `vs`, `env_b`] >> simp[]
QED

Theorem dynarray_snapshot_frontier:
  lookup_scopes name ei.scopes = SOME entry /\
  entry.type = ArrayTV tv (Dynamic c) /\ LENGTH vs <= c /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
  stmt_state_rel H ctx func cenv cx ei s ==>
  ?base. eval_operand (Var dp) s = SOME base /\
    w2n base + 32 + LENGTH vs * type_memory_size tv <= s.vs_alloca_next
Proof
  strip_tac >>
  `local_ptrs_rel func cenv ei.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `lookup_var dp s = SOME w0` >>
  qexists_tac `w0` >> simp[eval_operand_def] >>
  `32 + c * type_memory_size tv <= sz` by gvs[type_memory_size_def] >>
  `LENGTH vs * type_memory_size tv <= c * type_memory_size tv` by simp[] >>
  decide_tac
QED
