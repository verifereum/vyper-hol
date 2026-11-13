Theory targetIndexStorageFrame
Ancestors
  targetReachableInternalCallStorageFrame targetGuardedInternalCallStorageFrame targetTypedMutationStorageFrame
  targetStorageMutationDestination targetStorageReadRoot targetCallableAccessAlignment targetCallReachClosure
  vyperCallOutcomeFrame vyperValue vyperStoragePlaceRegion
  vyperTypeEvalSoundness vyperTypeEvalStoragePreservation vyperMachineFrame vyperTypeCallGraph
  vyperSubscriptOverlap vyperTypeSystem vyperInterpreter vyperEvalMisc supportedNames
  vyperTypeValues vyperTypeInvariants vyperTypeEnvPreservation
  vyperStorageLayoutSafety vyperStorageBackend vyperState bodySim list pred_set

Theorem semantic_expr_lists_DROP_members[local]:
  !n es.
    (!a. MEM a (accesses_exprs (DROP n es)) ==> MEM a (accesses_exprs es)) /\
    (!f. MEM f (int_calls_exprs (DROP n es)) ==> MEM f (int_calls_exprs es))
Proof
  Induct >> Cases >> simp[accesses_expr_def, int_calls_expr_def] >>
  metis_tac[]
QED

Theorem semantic_expr_lists_perm_members[local]:
  !xs ys. PERM xs ys ==>
    ((!a. MEM a (accesses_exprs xs) <=> MEM a (accesses_exprs ys)) /\
     (!f. MEM f (int_calls_exprs xs) <=> MEM f (int_calls_exprs ys)))
Proof
  ho_match_mp_tac sortingTheory.PERM_IND >>
  simp[accesses_expr_def, int_calls_expr_def] >> metis_tac[]
QED

Theorem semantic_accesses_named_MAP_SND[local]:
  !kes. accesses_exprs (MAP SND kes) = accesses_named_exprs kes
Proof
  Induct >> simp[accesses_expr_def] >>
  Cases_on `h` >> simp[accesses_expr_def]
QED

(* The protected declaration and call closure are fixed across the semantic
   induction; each recursive evaluator chooses its own typing environment. *)
Theorem guarded_storage_footprint_mutual[local]:
  !mods K mid name keys tr root rtv q.
  (!cx s. !env ret_ty env' st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_stmt s) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_stmt s) /\ ~MEM RiskyAcc (accesses_stmt s) /\
    type_stmt env ret_ty s = SOME env' /\ runtime_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx ss. !env ret_ty env' st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_stmts ss) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_stmts ss) /\ ~MEM RiskyAcc (accesses_stmts ss) /\
    type_stmts env ret_ty ss = SOME env' /\ runtime_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx it. !env ty st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_iterator it) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_iterator it) /\ ~MEM RiskyAcc (accesses_iterator it) /\
    well_typed_iterator env ty it /\ runtime_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_iterator it) /\
    eval_iterator cx it st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx tyv id body vs. !env ret_ty ty env' st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_stmts body) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_stmts body) /\ ~MEM RiskyAcc (accesses_stmts body) /\
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\ type_stmts (extend_local env id ty F) ret_ty body = SOME env' /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\ eval_for cx tyv id body vs st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx e. !env st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_expr e) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_expr e) /\ ~MEM RiskyAcc (accesses_expr e) /\
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx es. !env st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_exprs es) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_exprs es) /\ ~MEM RiskyAcc (accesses_exprs es) /\
    well_typed_exprs env es /\ runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_exprs cx es st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx bt. !env vt st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_target bt) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_target bt) /\ ~MEM RiskyAcc (accesses_target bt) /\
    type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx bt. !env ty st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_target bt) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_target bt) /\ ~MEM RiskyAcc (accesses_target bt) /\
    well_typed_target env bt ty /\ runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx g v. !env ty st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_atarget g) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_atarget g) /\ ~MEM RiskyAcc (accesses_atarget g) /\
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\ assign_tuple_targets cx g v st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx gs vs. !env tys st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_atargets gs) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_atargets gs) /\ ~MEM RiskyAcc (accesses_atargets gs) /\
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\ LIST_REL (value_runtime_typed env) tys vs /\
    runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\ assign_tuple_target_list cx gs vs st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr)) /\
  (!cx es. !env st res fin.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\ ~cx.in_deploy /\
    (!src ts. ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (supported_function_names ts)) /\
    storage_layout_safe cx /\
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= q /\ q < w2n root + type_slot_size rtv /\
    (!f g. MEM f K /\ MEM (f,g) (contract_call_edges mods) ==> MEM g K) /\
    (!f. MEM f K ==> ~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods f) /\
                       ~MEM RiskyAcc (function_accesses mods f)) /\
    (!f. MEM f (int_calls_exprs es) ==> MEM f K) /\
    ~MEM (WriteAcc (StateRef (mid,name))) (accesses_exprs es) /\ ~MEM RiskyAcc (accesses_exprs es) /\
    well_typed_exprs env es /\ runtime_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_expr_results cx es st = (res,fin) ==>
    lookup_storage (n2w q) (get_storage cx fin tr) = lookup_storage (n2w q) (get_storage cx st tr))
Proof
  let
    infix 1 via
    fun root g = (
  rpt gen_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >~ [`eval_stmt cx Pass st = (res,fin)`]
      >- (rpt strip_tac >> gvs[evaluate_def, return_def])
  >~ [`eval_stmt cx Continue st = (res,fin)`]
      >- (rpt strip_tac >> gvs[evaluate_def, raise_def])
  >~ [`eval_stmt cx Break st = (res,fin)`]
      >- (rpt strip_tac >> gvs[evaluate_def, raise_def])
  >~ [`eval_stmt cx (Return NONE) st = (res,fin)`]
      >- (gvs[evaluate_def, raise_def])
  >~ [`int_calls_stmt (Return (SOME e))`]
      >- run all_tac "Return"
  >~ [`eval_stmt cx (Raise RaiseBare) st = (res,fin)`]
      >- gvs[evaluate_def, raise_def]
  >~ [`eval_stmt cx (Raise RaiseUnreachable) st = (res,fin)`]
      >- gvs[evaluate_def, raise_def]
  >~ [`eval_stmts cx [] st = (res,fin)`]
      >- gvs[evaluate_def, return_def]
  >~ [`eval_exprs cx [] st = (res,fin)`]
      >- gvs[evaluate_def, return_def]
  >~ [`eval_expr_results cx [] st = (res,fin)`]
      >- gvs[evaluate_def, return_def]
  >~ [`assign_tuple_target_list cx [] [] st = (res,fin)`]
      >- gvs[evaluate_def, return_def]
  >~ [`assign_tuple_target_list cx [] (v::vs) st = (res,fin)`]
      >- gvs[evaluate_def, raise_def]
  >~ [`assign_tuple_target_list cx (g::gs) [] st = (res,fin)`]
      >- (rpt strip_tac >> gvs[evaluate_def, raise_def]) via "remaining"
) g

and branch prior "Return" g = (
  rpt strip_tac >>
  gvs[int_calls_stmt_def, int_calls_expr_def, accesses_stmt_def, type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  `lookup_storage (n2w q) (get_storage cx r tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (gvs[accesses_expr_def] >> first_x_assum irule >>
     rpt conj_tac >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- simp[] >> qexists_tac `env` >> simp[]) >>
  Cases_on `q'`
  >- (simp_tac bool_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
      Cases_on `read_result cx x r` >>
      drule read_result_state >> strip_tac >> gvs[] >>
      Cases_on `q'` >> simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[raise_def] >> rpt strip_tac >> gvs[]
) g

| branch prior "remaining" g = (
  prior >> rpt gen_tac >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac))
  >~ [`eval_target_place cx bt st = (res,fin)`]
      >- run all_tac "target_place" via "remaining2"
) g

| branch prior "target_place" g = (
  rpt strip_tac >> gvs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >>
  `lookup_storage (n2w q) (get_storage cx r tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >>
     rpt conj_tac >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- simp[] >> qexists_tac `env` >> simp[]) >>
  Cases_on `q'`
  >- (Cases_on `x` >> simp[get_place_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[raise_def] >> rpt strip_tac >> gvs[]
) g

| branch prior "remaining2" g = (
  prior
  >~ [`eval_expr cx (Call ty (IntCall (src,fn)) es ann) st = (res,fin)`]
      >- run all_tac "IntCall" via "remaining3"
) g

| branch prior "IntCall" g = (
  qpat_x_assum `well_typed_expr _ _ \/ _` mp_tac >>
  simp_tac bool_ss [type_place_expr_Call_IntCall_NONE, optionTheory.NOT_NONE_SOME,
    optionTheory.NOT_SOME_NONE] >> strip_tac >>
  rule_assum_tac (SIMP_RULE bool_ss [lift_option_type_INL_eq,
    type_check_def, assert_def, return_def, raise_def, get_scopes_def,
    set_scopes_def, push_function_def, bind_def, ignore_bind_def,
    pairTheory.pair_case_thm, sumTheory.sum_case_def, pairTheory.PAIR_EQ,
    sumTheory.INL_11, sumTheory.INR_11, sumTheory.INR_neq_INL,
    COND_RAND, COND_RATOR]) >>
  drule_at (Pat `eval_expr _ _ _ = _`) internal_call_storage_frame_reachable >>
  disch_then (qspecl_then [`n2w q`,`tr`,`env`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> simp[Excl "n2w_11"]
    >- (Cases_on `tr` >> simp_tac bool_ss [boolTheory.NOT_CLAUSES, boolTheory.OR_CLAUSES]
        >> gen_tac >> disch_tac >>
        irule targetCallLockFrameTheory.declared_capacity_lock_word_separation >>
        metis_tac[])
    >- (rpt strip_tac >>
        qpat_x_assum `!f. MEM f (int_calls_expr _) ==> _` mp_tac >>
        simp_tac (srw_ss()) [int_calls_expr_def] >> disch_tac >>
        qpat_x_assum `~MEM RiskyAcc (accesses_expr _)` mp_tac >>
        simp_tac (srw_ss()) [accesses_expr_def] >> disch_tac >>
        qpat_x_assum `~MEM (WriteAcc _) (accesses_expr _)` mp_tac >>
        simp_tac (srw_ss()) [accesses_expr_def] >> disch_tac >>
        first_assum irule >> simp[] >>
        rpt conj_tac >> metis_tac[])
    >- (rpt strip_tac >>
        rule_assum_tac (SIMP_RULE (srw_ss()) [get_storage_def]) >>
        simp_tac (srw_ss()) [get_storage_def] >>
        qpat_x_assum `!ts tup ast results aft.
          P ts tup ast results aft ==>
          !env st res fin. Q tup env st res fin ==>
            R fin = R st` mp_tac >>
        simp[get_storage_def] >>
        disch_then (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
        simp[oneline get_storage_def] >> disch_then irule >>
        simp[] >>
        `MEM (src,fn) K'` by
          (qpat_x_assum `!f. MEM f (int_calls_expr _) ==> _` mp_tac >>
           simp[int_calls_expr_def]) >>
        `ALOOKUP mods src = SOME ts` by
          (qpat_x_assum `get_module_code cx src = SOME ts` mp_tac >>
           simp[vyperContextTheory.get_module_code_def]) >>
        `ALL_DISTINCT (supported_function_names ts)` by metis_tac[] >>
        rpt conj_tac >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- run all_tac "defaults_calls"
        >- run all_tac "defaults_risky"
        >- run all_tac "defaults_write" >> metis_tac[]) >> run all_tac "call_body") >> simp[]
) g

| branch prior "defaults_calls" g = (
  rpt strip_tac >>
  `MEM f (int_calls_exprs dflts)` by
    metis_tac[semantic_expr_lists_DROP_members] >>
  drule vyperTypeContractStaticMapsTheory.lookup_callable_function_F_SOME_MEM >>
  strip_tac >>
  `MEM ((src,fn),f) (contract_call_edges mods)` by
    (irule vyperTypeCallGraphSoundnessTheory.contract_call_edges_function >>
     simp[function_int_calls_def] >>
     metis_tac[alistTheory.ALOOKUP_MEM]) >>
  metis_tac[]
) g

| branch prior "defaults_risky" g = (
  `~MEM RiskyAcc (function_accesses mods (src,fn))` by metis_tac[] >>
  spose_not_then assume_tac >>
  `MEM RiskyAcc (accesses_exprs dflts)` by
    metis_tac[semantic_expr_lists_DROP_members] >>
  `MEM RiskyAcc (function_accesses mods (src,fn))` by
    (irule callable_function_access_member >> simp[] >> metis_tac[]) >>
  metis_tac[]
) g

| branch prior "defaults_write" g = (
  `~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods (src,fn))` by metis_tac[] >>
  spose_not_then assume_tac >>
  `MEM (WriteAcc (StateRef (mid,name))) (accesses_exprs dflts)` by
    metis_tac[semantic_expr_lists_DROP_members] >>
  `MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods (src,fn))` by
    (irule callable_function_access_member >> simp[] >> metis_tac[]) >>
  metis_tac[]
) g

| branch prior "call_body" g = (
  rpt strip_tac >>
  qpat_x_assum `!ts tup a b c d e f g h i j k l m n zz.
    P ts tup a b c d e f g h i j k l m n zz ==>
    !env ret env' st res fin. Q tup env ret env' st res fin ==> R fin = R st` mp_tac >>
  simp[oneline get_storage_def] >>
  disch_then (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
  disch_then irule >>
  `LENGTH dflts + LENGTH es - LENGTH args =
   LENGTH dflts - (LENGTH args - LENGTH es)` by decide_tac >>
  qpat_x_assum `!ts tup a b c. P ts tup a b c ==> !env st res fin. _` kall_tac >>
  qpat_x_assum `!ts tup. P ts tup ==> !env st res fin. _` kall_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- run all_tac "body_calls"
  >- run all_tac "body_risky"
  >- run all_tac "body_write"
  >- (goal_assum (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `read_results _ _ _ = _`)) >>
      qpat_assum `LENGTH dflts + LENGTH es - LENGTH args = _`
        (fn th => once_rewrite_tac [th]) >>
      qexistsl [`prev_st`,`dst`,`dft`] >>
      qpat_x_assum `finally _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [ignore_bind_def])
  >- (goal_assum (drule_at Any))
  >- (goal_assum (drule_at Any)) >>
  goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >> simp[]
) g

| branch prior "body_calls" g = (
  rpt strip_tac >>
  `MEM (src,fn) K'` by
    (qpat_x_assum `!f. MEM f (int_calls_expr _) ==> _` mp_tac >>
     simp[int_calls_expr_def]) >>
  `ALOOKUP mods src = SOME ts` by
    (qpat_x_assum `get_module_code cx src = SOME ts` mp_tac >>
     simp[vyperContextTheory.get_module_code_def]) >>
  drule vyperTypeContractStaticMapsTheory.lookup_callable_function_F_SOME_MEM >>
  strip_tac >>
  `MEM ((src,fn),f) (contract_call_edges mods)` by
    (irule vyperTypeCallGraphSoundnessTheory.contract_call_edges_function >>
     simp[function_int_calls_def] >>
     metis_tac[alistTheory.ALOOKUP_MEM]) >>
  metis_tac[]
) g

| branch prior "body_risky" g = (
  `MEM (src,fn) K'` by
    (qpat_x_assum `!f. MEM f (int_calls_expr _) ==> _` mp_tac >>
     simp[int_calls_expr_def]) >>
  `ALOOKUP mods src = SOME ts` by
    (qpat_x_assum `get_module_code cx src = SOME ts` mp_tac >>
     simp[vyperContextTheory.get_module_code_def]) >>
  `~MEM RiskyAcc (function_accesses mods (src,fn))` by metis_tac[] >>
  spose_not_then assume_tac >>
  `MEM RiskyAcc (function_accesses mods (src,fn))` by
    (irule callable_function_access_member >> simp[] >> metis_tac[]) >>
  metis_tac[]
) g

| branch prior "body_write" g = (
  `MEM (src,fn) K'` by
    (qpat_x_assum `!f. MEM f (int_calls_expr _) ==> _` mp_tac >>
     simp[int_calls_expr_def]) >>
  `ALOOKUP mods src = SOME ts` by
    (qpat_x_assum `get_module_code cx src = SOME ts` mp_tac >>
     simp[vyperContextTheory.get_module_code_def]) >>
  `~MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods (src,fn))` by metis_tac[] >>
  spose_not_then assume_tac >>
  `MEM (WriteAcc (StateRef (mid,name))) (function_accesses mods (src,fn))` by
    (irule callable_function_access_member >> simp[] >> metis_tac[]) >>
  metis_tac[]
) g

| branch prior "remaining3" g = (
  prior
  >~ [`eval_expr cx (Name ann id) st = (res,fin)`]
    >- (drule vyperEvalMiscTheory.eval_expr_Name_preserves_state >> simp[])
  >~ [`eval_expr cx (Literal ann l) st = (res,fin)`]
    >- (gvs[Once evaluate_def, return_def])
  >~ [`eval_expr cx (Pop ann bt) st = (res,fin)`]
    >- run all_tac "pop" via "remaining4"
) g

| branch prior "pop" g = (
  `?n. well_typed_target env bt (ArrayT ann (Dynamic n))` by
    (gvs[Ntimes well_typed_expr_def 2, well_typed_target_def] >> metis_tac[]) >>
  qpat_x_assum `well_typed_expr _ _ \/ _` kall_tac >>
  fs[int_calls_expr_def, accesses_expr_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (rr,sm)` >>
  `lookup_storage (n2w q) (get_storage cx sm tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  reverse (Cases_on `rr`)
  >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >>
  Cases_on `x`
  >- run all_tac "pop_storage"
  >- (`machine_frame sm fin` by
        (mp_tac (Q.INST [`id` |-> `s`, `path` |-> `l`]
          machine_frame_pop_memory_place) >>
         simp[state_rel_frame_def] >>
         disch_then (qspec_then `sm` mp_tac) >> simp[]) >>
      Cases_on `tr` >> gvs[machine_frame_def, vyperStorageBackendTheory.get_storage_def]) >>
  run all_tac "pop_immutable"
) g

| branch prior "pop_storage" g = (
  rename1 `pop_place cx (StoragePlace tr0 slot tv) sm = (res,fin)` >>
  drule eval_target_place_storage_mutation_destination >> strip_tac >>
  Cases_on `tv` >> gvs[pop_place_def, raise_def] >>
  rename1 `ArrayTV elem bound` >> Cases_on `bound` >>
  gvs[pop_place_def, raise_def] >>
  `w2n root' + type_slot_size rtv' <= dimword(:256)` by
    (fs[storage_layout_safe_def] >> metis_tac[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root' + delta < dimword(:256)` by
    (fs[type_slot_size_def] >> decide_tac) >>
  `w2n (root' + n2w delta) = w2n root' + delta` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          arithmeticTheory.MOD_PLUS, arithmeticTheory.LESS_MOD] >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  `pop_place cx (StoragePlace tr0 (root' + n2w delta)
     (ArrayTV elem (Dynamic n'))) sm = (res,fin)` by simp[pop_place_def] >>
  `lookup_storage (n2w q) (get_storage cx fin tr) =
   lookup_storage (n2w q) (get_storage cx sm tr)` by
    (irule declared_capacity_pop_frame_result >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >> simp[]
) g

| branch prior "pop_immutable" g = (
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, bind_def, get_immutables_def, lift_option_type_def,
       lift_sum_def, set_immutable_def, return_def, raise_def,
       ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[get_address_immutables_def, set_address_immutables_def, return_def,
      lift_option_type_def, lift_sum_def,
      vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      raise_def, AllCaseEqs()] >> Cases_on `tr` >>
  gvs[vyperStorageBackendTheory.get_storage_def]
) g

| branch prior "remaining4" g = (
  prior
  >~ [`eval_base_place cx (NameTarget id) st = (res,fin)`] >-
    (drule eval_base_place_NameTarget_preserves_state >> simp[])
  >~ [`eval_base_place cx (TopLevelNameTarget nsid) st = (res,fin)`] >-
    (drule eval_base_place_TopLevelNameTarget_preserves_state >> simp[])
  via "remaining5"
) g

| branch prior "remaining5" g = (
  prior
  >~ [`eval_expr_results cx (e::es) st = (res,fin)`] >-
    run all_tac "expr_results_cons"
  via "remaining6"
) g

| branch prior "expr_results_cons" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Once well_typed_expr_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  disch_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!env' st' res fin'. _` (qspecl_then [`env`,`st`] mp_tac) >>
  simp[] >> disch_then (drule_at Any) >> disch_tac >>
  drule_all eval_expr_preserves_runtime_consistent >> disch_tac >>
  gvs[] >> metis_tac[]
) g

| branch prior "remaining6" g = (
  prior
  >~ [`eval_iterator cx (Array e) st = (res,fin)`] >-
    run all_tac "iterator_array"
  via "remaining7"
) g

| branch prior "iterator_array" g = (
  gvs[accesses_iterator_def, int_calls_iterator_def, well_typed_iterator_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[lift_option_type_def, lift_sum_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[]
) g

| branch prior "remaining7" g = (
  prior
  >~ [`eval_exprs cx (e::es) st = (res,fin)`] >-
    run all_tac "exprs_cons"
  via "remaining8"
) g

| branch prior "exprs_cons" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Once well_typed_expr_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  disch_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!env' st' res fin'. _` (qspecl_then [`env`,`st`] mp_tac) >>
  simp[] >> disch_then (drule_at Any) >> disch_tac >>
  drule_all eval_expr_preserves_runtime_consistent >> disch_tac >>
  gvs[] >> metis_tac[]
) g

| branch prior "remaining8" g = (
  prior
  >~ [`eval_expr cx (TopLevelName ann (src,id)) st = (res,fin)`] >-
    (gvs[Once evaluate_def] >>
     drule vyperStatePreservationTheory.lookup_global_state >> simp[])
  via "remaining9"
) g

| branch prior "remaining9" g = (
  prior
  >~ [`eval_expr cx (FlagMember ann nsid memid) st = (res,fin)`] >-
    (PairCases_on `nsid` >>
     gvs[Once evaluate_def, lookup_flag_mem_def,
         vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()])
  via "remaining10"
) g

| branch prior "remaining10" g = (
  prior
  >~ [`eval_expr cx (Attribute ann e id) st = (res,fin)`] >-
    run all_tac "expr_attribute"
  via "remaining11"
) g

| branch prior "expr_attribute" g = (
  gvs[accesses_expr_def, int_calls_expr_def] >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
) g

| branch prior "remaining11" g = (
  prior
  >~ [`eval_expr cx (Call ann RawLog es drv) st = (res,fin)`] >-
    run all_tac "raw_log"
  via "remaining12"
) g

| branch prior "raw_log" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Once well_typed_expr_def,
      AllCaseEqs()] >> gvs[Once well_typed_expr_def] >>
  qpat_x_assum `eval_expr _ (Call _ RawLog _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, check_def, check_not_static_def, push_log_def,
       lift_option_type_def, lift_sum_def, vyperMiscTheory.option_CASE_rator,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `tr` >>
  gvs[vyperStorageBackendTheory.get_storage_def] >>
  qpat_x_assum `!env' st' res fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
                          first_assum MATCH_ACCEPT_TAC)) >> simp[]
) g

| branch prior "remaining12" g = (
  prior
  >~ [`eval_expr cx (Call ann RawRevert es drv) st = (res,fin)`] >-
    run all_tac "raw_revert"
  via "remaining13"
) g

| branch prior "raw_revert" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Once well_typed_expr_def,
      AllCaseEqs()] >> gvs[Once well_typed_expr_def] >>
  qpat_x_assum `eval_expr _ (Call _ RawRevert _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, check_def, lift_option_type_def,
       lift_sum_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
) g

| branch prior "remaining13" g = (
  prior
  >~ [`eval_expr cx (Call ann SelfDestructTarget es drv) st = (res,fin)`] >-
    run all_tac "self_destruct"
  via "remaining14"
) g

| branch prior "self_destruct" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Once well_typed_expr_def,
      AllCaseEqs()] >> gvs[Once well_typed_expr_def] >>
  qpat_x_assum `eval_expr _ (Call _ SelfDestructTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, check_def, check_not_static_def,
       transfer_value_def, get_accounts_def, update_accounts_def,
       lift_option_type_def, lift_sum_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  gvs[COND_RATOR, bind_def, return_def, assert_def, get_accounts_def,
      update_accounts_def, AllCaseEqs()] >> Cases_on `tr` >>
  gvs[vyperStorageBackendTheory.get_storage_def] >>
  qpat_x_assum `!env' st' res fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
                          first_assum MATCH_ACCEPT_TAC)) >>
  simp[vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def]
) g

| branch prior "remaining14" g = (
  prior
  >~ [`eval_expr cx (Subscript ann e idx) st = (res,fin)`] >-
    run all_tac "expr_subscript"
  via "remaining15"
) g

| branch prior "expr_subscript" g = (
  gvs[accesses_expr_def, int_calls_expr_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  disch_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  fs[Once well_typed_expr_def] >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `!env' st' res' fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >>
  disch_then (drule_at Any) >> disch_tac >>
  `runtime_consistent env cx (SND (eval_expr cx e st))` by
    (irule eval_expr_place_preserves_runtime_consistent >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
) g

| branch prior "remaining15" g = (
  prior
  >~ [`eval_expr cx (Builtin ann bt es) st = (res,fin)`] >-
    run all_tac "expr_builtin"
  via "remaining16"
) g

| branch prior "expr_builtin" g = (
  gvs[accesses_expr_def, int_calls_expr_def] >>
  Cases_on `bt = Len` >- run all_tac "builtin_len" >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >- run all_tac "builtin_membership" >>
  Cases_on `bt = Env MsgGas` >- run all_tac "builtin_gas" >>
  run all_tac "builtin_other"
) g

| branch prior "builtin_len" g = (
  prior >> gvs[] >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[type_check_def, assert_def, return_def,
    raise_def, bind_def, AllCaseEqs()] >>
  imp_res_tac vyperStatePreservationTheory.result_array_length_state >> gvs[] >>
  fs[Once well_typed_expr_def] >>
  Cases_on `es` >> gvs[vyperContextTheory.builtin_args_length_ok_def,
    Once well_typed_expr_def, accesses_expr_def, int_calls_expr_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
) g

| branch prior "builtin_membership" g = (
  prior >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, AllCaseEqs()] >> rpt strip_tac >>
  fs[return_def, raise_def, lift_option_type_def, lift_sum_def] >>
  fs[Once well_typed_expr_def] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, type_check_def, assert_def, AllCaseEqs()] >>
  qpat_x_assum `!env' st' res fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
                          first_assum MATCH_ACCEPT_TAC)) >> simp[]
) g

| branch prior "builtin_gas" g = (
  prior >> gvs[] >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
  Cases_on `tr` >> gvs[vyperStorageBackendTheory.get_storage_def]
) g

| branch prior "builtin_other" g = (
  prior >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, AllCaseEqs()] >> rpt strip_tac >>
  fs[] >>
  gvs[get_accounts_def, lift_sum_def, return_def, raise_def] >>
  imp_res_tac vyperStatePreservationTheory.precompile_call_success_state >>
  gvs[] >> fs[Once well_typed_expr_def] >>
  gvs[vyperMiscTheory.sum_CASE_rator, return_def, raise_def,
      type_check_def, assert_def, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[vyperStorageBackendTheory.get_storage_def] >>
  qpat_x_assum `!env' st' res fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
                          first_assum MATCH_ACCEPT_TAC)) >> simp[]
) g

| branch prior "remaining16" g = (
  prior
  >~ [`eval_base_place cx (SubscriptTarget bt e) st = (res,fin)`] >-
    run all_tac "base_subscript"
  via "remaining17"
) g

| branch prior "base_subscript" g = (
  gvs[accesses_expr_def, int_calls_expr_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  disch_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  fs[vyperTypeEnvTheory.type_place_target_SubscriptTarget] >>
  imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
  drule_all vyperTypeEvalStoragePreservationTheory.eval_base_place_preserves_runtime_consistent >>
  disch_tac >>
  qpat_x_assum `!env' vt' st' res' fin'. _`
    (qspecl_then [`env`,`vt'`,`st`] mp_tac) >>
  simp[] >> disch_tac >> metis_tac[]
) g

| branch prior "remaining17" g = (
  prior
  >~ [`eval_base_place cx (AttributeTarget bt id) st = (res,fin)`] >-
    (gvs[accesses_expr_def, int_calls_expr_def] >>
     qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >>
     imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
     fs[vyperTypeEnvTheory.type_place_target_AttributeTarget] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining18"
) g

| branch prior "remaining18" g = (
  prior
  >~ [`eval_expr cx (Name ty id) st = (res,fin)`] >-
    (gvs[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
         type_check_def, assert_def, lift_option_type_def,
         return_def, raise_def, AllCaseEqs()]) via "remaining19"
) g

| branch prior "remaining19" g = (
  prior
  >~ [`eval_expr cx (Literal ty lit) st = (res,fin)`] >-
    (qpat_x_assum `eval_expr _ (Literal _ _) _ = _` mp_tac >>
     simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]) via "remaining20"
) g

| branch prior "remaining20" g = (
  prior
  >~ [`eval_iterator cx (Range e e') st = (res,fin)`] >-
    run all_tac "iterator_range" via "remaining21"
) g

| branch prior "iterator_range" g = (
  gvs[accesses_iterator_def, int_calls_iterator_def, well_typed_iterator_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >> disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >> disch_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
  gvs[lift_sum_def, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule_all vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent >>
  disch_tac >>
  qpat_x_assum `!env' st' res fin'. _`
    (qspecl_then [`env`,`st`] mp_tac) >> simp[] >> disch_tac >>
  metis_tac[]
) g

| branch prior "remaining21" g = (
  prior
  >~ [`assign_tuple_targets cx (TupleTarget gs) v st = (res,fin)`] >-
    run all_tac "tuple_targets" via "remaining22"
) g

| branch prior "tuple_targets" g = (
  gvs[well_typed_atarget_def, accesses_atarget_def, int_calls_atarget_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
) g

| branch prior "remaining22" g = (
  prior
  >~ [`eval_stmt cx (Expr e) st = (res,fin)`] >-
    (gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def] >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >>
     gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining23"
) g

| branch prior "remaining23" g = (
  prior
  >~ [`eval_stmt cx (Raise (RaiseReason e)) st = (res,fin)`] >-
    (gvs[accesses_stmt_def, int_calls_stmt_def, accesses_raise_reason_def,
         int_calls_raise_reason_def, type_stmt_def] >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >> imp_res_tac read_result_state >>
     gvs[lift_option_type_def, vyperMiscTheory.option_CASE_rator,
         return_def, raise_def, AllCaseEqs()] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining24"
) g

| branch prior "remaining24" g = (
  prior
  >~ [`eval_stmt cx (Assert e AssertBare) st = (res,fin)`] >-
    (gvs[accesses_stmt_def, int_calls_stmt_def, accesses_assert_reason_def,
         int_calls_assert_reason_def, type_stmt_def] >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def, raise_def,
          AllCaseEqs()] >>
     rpt strip_tac >> imp_res_tac read_result_state >>
     gvs[lift_option_type_def, vyperMiscTheory.option_CASE_rator,
         return_def, raise_def, AllCaseEqs()] >>
     gvs[COND_RATOR, return_def, raise_def, AllCaseEqs()] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining25"
) g

| branch prior "remaining25" g = (
  prior
  >~ [`eval_stmt cx (Assert e AssertUnreachable) st = (res,fin)`] >-
    (gvs[accesses_stmt_def, int_calls_stmt_def, accesses_assert_reason_def,
         int_calls_assert_reason_def, type_stmt_def] >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def, raise_def,
          AllCaseEqs()] >>
     rpt strip_tac >> imp_res_tac read_result_state >>
     gvs[lift_option_type_def, vyperMiscTheory.option_CASE_rator,
         return_def, raise_def, AllCaseEqs()] >>
     gvs[COND_RATOR, return_def, raise_def, AllCaseEqs()] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining26"
) g

| branch prior "remaining26" g = (
  prior
  >~ [`eval_stmt cx (Raise (RaiseCustomError err)) st = (res,fin)`] >-
    (gvs[accesses_stmt_def, int_calls_stmt_def, accesses_raise_reason_def,
         int_calls_raise_reason_def, type_stmt_def, well_typed_custom_error_def] >>
     Cases_on `err` >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >>
     gvs[vyperMiscTheory.option_CASE_rator, bind_def, lift_option_def,
         return_def, raise_def, AllCaseEqs()] >>
     drule vyperASTTheory.order_custom_error_args_perm >> strip_tac >>
     drule semantic_expr_lists_perm_members >> strip_tac >>
     `well_typed_exprs env es` by metis_tac[well_typed_exprs_perm] >>
     `call_evaluation_safe cx (int_calls_exprs es)` by
       metis_tac[call_evaluation_safe_exprs_perm] >>
     first_x_assum irule >> simp[] >> metis_tac[]) via "remaining27"
) g

| branch prior "remaining27" g = (
  prior
  >~ [`assign_tuple_targets cx (BaseTarget bt) v st = (res,fin)`] >-
    (gvs[accesses_atarget_def, int_calls_atarget_def, well_typed_atarget_def] >>
     qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]
     >~ [`eval_target_place cx bt st = (INR ex,fin)`] >-
       (first_x_assum irule >> simp[] >> metis_tac[]) >>
     `lookup_storage (n2w q) (get_storage cx s'' tr) =
      lookup_storage (n2w q) (get_storage cx st tr)` by
       (first_x_assum irule >> simp[] >> metis_tac[]) >>
     Cases_on `p`
     >- run all_tac "tuple_base_storage" >>
     run all_tac "tuple_base_nonstorage") via "remaining28"
) g

| branch prior "tuple_base_storage" g = (
  drule_all eval_target_place_success_storage_type >>
  simp[vyperTypeInvariantsTheory.eval_result_typed_def,
       vyperTypeInvariantsTheory.runtime_place_typed_def,
       place_type_value_def, return_def] >> strip_tac >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  drule eval_target_place_storage_mutation_destination >> strip_tac >>
  `((mid',name',keys') <> (mid,name,keys))` by
    (strip_tac >> gvs[]) >>
  gvs[write_place_def] >>
  Cases_on `type_slot_size t = 0`
  >- (drule_all vyperStorageRegionWriteTheory.typed_zero_storage_write_footprint >>
      strip_tac >> gvs[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root' + type_slot_size rtv' <= dimword(:256)` by
    metis_tac[storage_layout_safe_region_nonoverflow] >>
  `w2n (root' + n2w delta) = w2n root' + delta` by
    (`delta < dimword(:256) /\ w2n root' + delta < dimword(:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `lookup_storage (n2w q) (get_storage cx fin tr) =
   lookup_storage (n2w q) (get_storage cx s'' tr)` by
    (irule declared_capacity_typed_write_frame_result >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  simp[]
) g

| branch prior "tuple_base_nonstorage" g = (
  prior
  >~ [`write_place cx (MemoryPlace id path) v s'' = (res,fin)`] >-
    (mp_tac machine_frame_write_memory_place >>
     simp[state_rel_frame_def] >> disch_then (qspec_then `s''` mp_tac) >>
     simp[machine_frame_def, get_storage_def] >>
     strip_tac >> Cases_on `tr` >> gvs[get_storage_def]) >>
  gvs[write_place_def, bind_def, get_immutables_def, set_immutable_def,
      lift_option_type_def, lift_sum_def, type_check_def, assert_def,
      return_def, raise_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), get_storage_def] >>
  gvs[get_address_immutables_def, bind_def, return_def, raise_def,
      get_accounts_def, lift_option_type_def, set_address_immutables_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining28" g = (
  prior
  >~ [`eval_expr cx (StructLit ann sid kes) st = (res,fin)`] >-
    (PairCases_on `sid` >>
     gvs[accesses_expr_def, int_calls_expr_def, Ntimes well_typed_expr_def 2] >>
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     drule vyperTypeEvalSoundnessTheory.well_typed_named_exprs_MAP_SND_stmt >> strip_tac >>
     first_x_assum irule >>
     simp[int_calls_exprs_MAP_SND, semantic_accesses_named_MAP_SND] >>
     metis_tac[]) via "remaining29"
) g

| branch prior "remaining29" g = (
  prior
  >~ [`eval_expr cx (Call ty (RawCallCalldataTarget flags) es opts) st = (res,fin)`] >-
    (gvs[accesses_expr_def, risky_call_target_def]) via "remaining30"
) g

| branch prior "remaining30" g = (
  prior
  >~ [`eval_expr cx (Call ty (RawCallTarget flags) es opts) st = (res,fin)`] >-
    (gvs[accesses_expr_def, risky_call_target_def]) via "remaining31"
) g

| branch prior "remaining31" g = (
  prior
  >~ [`eval_expr cx (Call ty (Send gas) es opts) st = (res,fin)`] >-
    (gvs[accesses_expr_def, risky_call_target_def]) via "remaining32"
) g

| branch prior "remaining32" g = (
  prior
  >~ [`eval_expr cx (IfExp ty e et ef) st = (res,fin)`] >-
    run all_tac "if_expr" via "remaining33"
) g

| branch prior "if_expr" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Ntimes well_typed_expr_def 2] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  `lookup_storage (n2w q) (get_storage cx r tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]) >>
  Cases_on `q'`
  >- (`call_evaluation_safe cx (int_calls_expr e)` by
        metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left] >>
      `runtime_consistent env cx r` by
        metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
      simp[return_def, switch_BoolV_def, bind_def] >>
      Cases_on `read_result cx x r` >>
      drule read_result_state >> strip_tac >> gvs[] >>
      Cases_on `q'` >> simp[raise_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
      imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[] >>
      Cases_on `x' = BoolV T` >> fs[raise_def] >>
      Cases_on `x' = BoolV F` >> fs[raise_def] >>
      metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
                vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]) >>
  simp[raise_def] >> rpt strip_tac >> gvs[]
) g

| branch prior "remaining33" g = (
  prior
  >~ [`eval_expr cx (TypeBuiltin ann tb typ es) st = (res,fin)`] >-
    run all_tac "type_builtin" via "remaining34"
) g

| branch prior "type_builtin" g = (
  gvs[accesses_expr_def, int_calls_expr_def, Ntimes well_typed_expr_def 2] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)`
  >- (qpat_x_assum `do _ od st = _` mp_tac >>
      simp[bind_def, ignore_bind_def, assert_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`st`,`st`] mp_tac) >>
      simp[type_check_def, assert_def, return_def] >>
      disch_then irule >> simp[] >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      metis_tac[]) >>
  gvs[assert_def, bind_def, ignore_bind_def, raise_def]
) g

| branch prior "remaining34" g = (
  prior
  >~ [`eval_expr cx (TopLevelName ann (src,id)) st = (res,fin)`] >-
    (gvs[Once evaluate_def] >>
     mp_tac machine_frame_lookup_global >>
     simp[state_rel_frame_def] >> disch_then (qspec_then `st` mp_tac) >>
     simp[machine_frame_def] >> strip_tac >> Cases_on `tr` >>
     gvs[get_storage_def]) via "remaining35"
) g

| branch prior "remaining35" g = (
  prior
  >~ [`eval_expr cx (FlagMember aann nnsid mmember) st = (res,fin)`] >-
    gvs[Once well_typed_expr_def] via "remaining36"
) g

| branch prior "remaining36" g = (
  prior
  >~ [`eval_stmt cx (Assign (BaseTarget bt) e) st = (res,fin)`] >-
    run all_tac "assign_base" via "remaining37"
) g

| branch prior "assign_base" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
  >~ [`eval_expr cx e st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  imp_res_tac read_result_state >> gvs[] >>
  `runtime_consistent env cx s''` by
    metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
  drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >> strip_tac >>
  gvs[well_typed_atarget_def, accesses_atarget_def, int_calls_atarget_def] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left] >>
  qpat_x_assum `!s'' pv t' s'3' v t''. _` drule >>
  disch_then drule >> strip_tac
  >~ [`eval_target_place cx bt s'' = (INR ex,fin)`] >-
    (qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _`
       (SUBST1_TAC o SYM) >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'4' tr) =
   lookup_storage (n2w q) (get_storage cx s'' tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `p` >- run all_tac "assign_base_storage" >>
  run all_tac "assign_base_nonstorage"
) g

| branch prior "assign_base_storage" g = (
  `value_runtime_typed env (expr_type e) v''` by
    (drule_all eval_expr_success_storage_facts >> strip_tac >>
     fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env ty v''` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
      vyperTypeInvariantsTheory.runtime_place_typed_def,
      place_type_value_def, return_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  drule eval_target_place_storage_mutation_destination >> strip_tac >>
  `((mid',name',keys') <> (mid,name,keys))` by (strip_tac >> gvs[]) >>
  gvs[write_place_def] >>
  Cases_on `type_slot_size t = 0`
  >- (drule_all vyperStorageRegionWriteTheory.typed_zero_storage_write_footprint >>
      strip_tac >> gvs[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root' + type_slot_size rtv' <= dimword(:256)` by
    metis_tac[storage_layout_safe_region_nonoverflow] >>
  `w2n (root' + n2w delta) = w2n root' + delta` by
    (`delta < dimword(:256) /\ w2n root' + delta < dimword(:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `lookup_storage (n2w q) (get_storage cx fin tr) =
   lookup_storage (n2w q) (get_storage cx s'4' tr)` by
    (irule declared_capacity_typed_write_frame_result >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >> simp[]
) g

| branch prior "assign_base_nonstorage" g = (
  prior >>
  qpat_x_assum `!env st res fin. _` kall_tac >>
  qpat_x_assum `!env st res fin. _` kall_tac
  >~ [`write_place cx (MemoryPlace id path) v s'4' = (res,fin)`] >-
    (mp_tac machine_frame_write_memory_place >>
     simp[state_rel_frame_def] >> disch_then (qspec_then `s'4'` mp_tac) >>
     simp[machine_frame_def, get_storage_def] >>
     strip_tac >> Cases_on `tr` >> gvs[get_storage_def]) >>
  gvs[write_place_def, bind_def, get_immutables_def, set_immutable_def,
      lift_option_type_def, lift_sum_def, type_check_def, assert_def,
      return_def, raise_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), get_storage_def] >>
  gvs[get_address_immutables_def, bind_def, return_def, raise_def,
      get_accounts_def, lift_option_type_def, set_address_immutables_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining37" g = (
  prior
  >~ [`eval_stmt cx (Append bt e) st = (res,fin)`] >- run all_tac "append_stmt" via "remaining38"
) g

| branch prior "append_stmt" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_target_place cx bt st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env cx s''` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     metis_tac[cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))]) >>
  qpat_x_assum `!s'' p t'. eval_target_place _ _ _ = _ ==> _` drule >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
  >~ [`eval_expr cx e s'' = (INR ex,fin)`] >-
    (qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _`
       (SUBST1_TAC o SYM) >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'3' tr) =
   lookup_storage (n2w q) (get_storage cx s'' tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `p` >- run all_tac "append_storage" >> run all_tac "append_nonstorage"
) g

| branch prior "append_storage" g = (
  `value_runtime_typed env (expr_type e) v'3'` by
    (drule_all eval_expr_success_storage_facts >> strip_tac >>
     fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env elem_ty v'3'` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
      vyperTypeInvariantsTheory.runtime_place_typed_def,
      place_type_value_def, return_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  drule eval_target_place_storage_mutation_destination >> strip_tac >>
  `((mid',name',keys') <> (mid,name,keys))` by (strip_tac >> gvs[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root' + type_slot_size rtv' <= dimword(:256)` by
    metis_tac[storage_layout_safe_region_nonoverflow] >>
  `w2n (root' + n2w delta) = w2n root' + delta` by
    (`delta < dimword(:256) /\ w2n root' + delta < dimword(:256)` by
       (gvs[type_slot_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `lookup_storage (n2w q) (get_storage cx fin tr) =
   lookup_storage (n2w q) (get_storage cx s'3' tr)` by
    (irule declared_capacity_append_frame_result >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >> simp[]
) g

| branch prior "append_nonstorage" g = (
  prior >>
  qpat_x_assum `!env'' ty st' res fin'. _` kall_tac >>
  qpat_x_assum `!env'' st' res fin'. _` kall_tac
  >~ [`append_place cx (MemoryPlace id path) v s'3' = (res,fin)`] >-
    (mp_tac machine_frame_append_memory_place >>
     simp[state_rel_frame_def] >> disch_then (qspec_then `s'3'` mp_tac) >>
     simp[machine_frame_def] >> strip_tac >> Cases_on `tr` >> gvs[get_storage_def]) >>
  gvs[append_place_def, raise_def, bind_def, place_type_value_def,
      return_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> gvs[] >>
  gvs[write_place_def, bind_def, get_immutables_def, set_immutable_def,
      lift_option_type_def, lift_sum_def, type_check_def, assert_def,
      return_def, raise_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), get_storage_def] >>
  gvs[get_address_immutables_def, bind_def, return_def, raise_def,
      get_accounts_def, lift_option_type_def, set_address_immutables_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining38" g = (
  prior
  >~ [`eval_stmt cx (Assert e (AssertReason reason)) st = (res,fin)`] >-
    run all_tac "assert_reason" via "remaining39"
) g

| branch prior "assert_reason" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  gvs[int_calls_assert_reason_def, accesses_assert_reason_def] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_expr cx e st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env cx s''` by
    metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
  qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _` drule >> strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `v' = BoolV T` >> gvs[return_def] >>
  Cases_on `v' = BoolV F` >> gvs[raise_def] >>
  qpat_x_assum `do _ od s'' = _` mp_tac >>
  simp[bind_def, raise_def, return_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _`
    (SUBST1_TAC o SYM) >>
  first_x_assum irule >> simp[] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
) g

| branch prior "remaining39" g = (
  prior
  >~ [`eval_stmt cx (Assign (TupleTarget gs) e) st = (res,fin)`] >-
    run all_tac "assign_tuple_stmt" via "remaining40"
) g

| branch prior "assign_tuple_stmt" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
  >~ [`eval_expr cx e st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  imp_res_tac read_result_state >> gvs[] >>
  `runtime_consistent env cx s''` by
    metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
  `value_runtime_typed env (expr_type e) v''` by
    (drule_all eval_expr_success_storage_facts >> strip_tac >>
     fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >> strip_tac >>
  `value_runtime_typed env ty v''` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  qpat_x_assum `!s'' tv t s'3' v t'. _` drule >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _` (SUBST1_TAC o SYM) >>
  first_x_assum irule >> simp[] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
) g

| branch prior "remaining40" g = (
  prior
  >~ [`eval_stmt cx (Assert e (AssertCustomError err)) st = (res,fin)`] >-
    run all_tac "assert_custom" via "remaining41"
) g

| branch prior "assert_custom" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def,
      accesses_assert_reason_def, int_calls_assert_reason_def,
      well_typed_custom_error_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_expr cx e st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env cx s''` by
    metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `v' = BoolV T` >> gvs[return_def] >>
  Cases_on `v' = BoolV F` >> gvs[raise_def] >>
  Cases_on `err` >>
  gvs[vyperMiscTheory.option_CASE_rator, bind_def, lift_option_def,
      return_def, raise_def, AllCaseEqs()] >>
  drule vyperASTTheory.order_custom_error_args_perm >> strip_tac >>
  drule semantic_expr_lists_perm_members >> strip_tac >>
  `well_typed_exprs env es` by metis_tac[well_typed_exprs_perm] >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    metis_tac[call_evaluation_safe_exprs_perm,
      vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right] >>
  qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _` drule >> strip_tac >>
  qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _` (SUBST1_TAC o SYM) >>
  first_x_assum irule >> simp[] >> metis_tac[]
) g

| branch prior "remaining41" g = (
  prior
  >~ [`eval_stmts cx (s::ss) st = (res,fin)`] >- run all_tac "stmts_cons" via "remaining42"
) g

| branch prior "stmts_cons" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `do _ od st = _` mp_tac >>
  simp[ignore_bind_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_stmt cx s st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env'' cx s''` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >> simp[]) >>
  qpat_x_assum `!s'' t. eval_stmt cx s s'' = (INL (),t) ==> _` drule >> strip_tac >>
  qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _` (SUBST1_TAC o SYM) >>
  first_x_assum irule >> simp[] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
) g

| branch prior "remaining42" g = (
  prior
  >~ [`eval_stmt cx (Log id es) st = (res,fin)`] >- run all_tac "log_stmt" via "remaining43"
) g

| branch prior "log_stmt" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >~ [`eval_exprs cx es st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!env'' st' res fin'. _` kall_tac >>
  gvs[lift_option_def, vyperMiscTheory.option_CASE_rator, bind_def,
      ignore_bind_def, check_not_static_def, check_def, push_log_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining43" g = (
  prior
  >~ [`assign_tuple_target_list cx (g::gs) (v::vs) st = (res,fin)`] >-
    run all_tac "tuple_list_cons" via "remaining44"
) g

| branch prior "tuple_list_cons" g = (
  Cases_on `tys` >>
  gvs[accesses_atarget_def, int_calls_atarget_def] >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `do _ od st = _` mp_tac >>
  simp[ignore_bind_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_atarget g)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`assign_tuple_targets cx g v st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env cx s''` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     metis_tac[cj 9 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual]) >>
  qpat_x_assum `!s'' t. assign_tuple_targets cx g v s'' = (INL (),t) ==> _` drule >>
  strip_tac >>
  qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _` (SUBST1_TAC o SYM) >>
  first_x_assum irule >> simp[] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
) g

| branch prior "remaining44" g = (
  prior
  >~ [`eval_stmt cx (AnnAssign id typ e) st = (res,fin)`] >- run all_tac "annassign" via "remaining45"
) g

| branch prior "annassign" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, lift_option_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def] >>
  qpat_x_assum `!s'' tyv t. _` (mp_tac o SRULE [lift_option_type_def, lift_option_def,
      return_def, raise_def]) >> simp[] >> strip_tac
  >~ [`eval_expr cx e s'' = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'3' tr) =
   lookup_storage (n2w q) (get_storage cx s'' tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  imp_res_tac read_result_state >> gvs[] >>
  mp_tac (Q.INST [`nm` |-> `id`, `tv` |-> `tyv`, `v` |-> `v'3'`]
    machine_frame_new_variable) >>
  simp[state_rel_frame_def] >>
  disch_then (qspec_then `s'3'` mp_tac) >>
  simp[machine_frame_def] >> strip_tac >> Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining45" g = (
  prior
  >~ [`eval_stmt cx (If e ss ss') st = (res,fin)`] >- run all_tac "if_stmt" via "remaining46"
) g

| branch prior "if_stmt" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_expr cx e st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `runtime_consistent env cx s''` by
    metis_tac[vyperTypeEvalStoragePreservationTheory.eval_expr_preserves_runtime_consistent] >>
  qpat_x_assum `do _ od s'' = _` mp_tac >>
  simp[ignore_bind_def, bind_def, push_scope_def, get_scopes_def,
       set_scopes_def, return_def, finally_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `runtime_consistent env cx (s'' with scopes updated_by CONS FEMPTY)` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     metis_tac[vyperTypeEnvPreservationTheory.push_scope_env_consistent,
       vyperTypeStatePreservationTheory.push_scope_preserves_state_well_typed,
       push_scope_def, return_def]) >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!s'' tv t s'3' t'. _ /\ _ ==> _`
    (mp_tac o SRULE [push_scope_def, return_def]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `!s'' tv t s'3' t'. _ /\ _ ==> _`
    (mp_tac o SRULE [push_scope_def, return_def]) >>
  disch_then drule >> strip_tac >>
  prior >>~- ([`(if _ then _ else _) _ = _`],
    qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
    simp[COND_RATOR, AllCaseEqs(), raise_def] >> rpt strip_tac >>
    run all_tac "if_live") >>
  run all_tac "if_error"
) g

| branch prior "if_live" g = (
  prior >>
  `call_evaluation_safe cx (int_calls_stmts ss) /\
   call_evaluation_safe cx (int_calls_stmts ss')` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
      vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right] >>
  prior >>~- ([`eval_stmts cx branch (s'' with scopes updated_by CONS FEMPTY) = (r,sm)`],
    rename1 `eval_stmts cx branch (s'' with scopes updated_by CONS FEMPTY) = (r,sm)` >>
    `lookup_storage (n2w q) (get_storage cx sm tr) =
     lookup_storage (n2w q) (get_storage cx (s'' with scopes updated_by CONS FEMPTY) tr)` by
      (qpat_x_assum `!a b c d e f. _ /\ _ /\ type_stmts a b branch = SOME c /\ _ ==> _` irule >>
       simp[] >> Cases_on `type_stmts env ret_ty branch` >> fs[] >> metis_tac[]) >>
    run all_tac "if_pop") >>
  run all_tac "if_immediate"
) g

| branch prior "if_pop" g = (
  prior >>
  rpt (qpat_x_assum `!a. _` kall_tac) >>
  qpat_x_assum `pop_scope _ = _` mp_tac >>
  simp[pop_scope_def, get_scopes_def, set_scopes_def, bind_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `tr` >> gvs[get_storage_def, raise_def]
) g

| branch prior "if_immediate" g = (
  prior >>
  rpt (qpat_x_assum `!a. _` kall_tac) >>
  gvs[] >>
  qpat_x_assum `pop_scope _ = _` mp_tac >>
  simp[pop_scope_def, get_scopes_def, set_scopes_def, bind_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `tr` >> gvs[get_storage_def, raise_def]
) g

| branch prior "if_error" g = (
  prior >>
  rpt (qpat_x_assum `!a. _` kall_tac) >>
  gvs[pop_scope_def, get_scopes_def, set_scopes_def, bind_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining46" g = (
  prior
  >~ [`eval_for cx tyv id body' [] st = (res,fin)`] >-
    gvs[Once evaluate_def, return_def] via "remaining47"
) g

| branch prior "remaining47" g = (
  prior
  >~ [`eval_stmt cx (AugAssign ty bt bop e) st = (res,fin)`] >- run all_tac "augassign" via "remaining48"
) g

| branch prior "augassign" g = (
  gvs[accesses_stmt_def, int_calls_stmt_def, type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> fs[] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]
  >~ [`eval_target_place cx bt st = (INR ex,fin)`] >-
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `lookup_storage (n2w q) (get_storage cx s'' tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  fs[] >>
  `runtime_consistent env cx s''` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     metis_tac[cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))]) >>
  qpat_x_assum `!s'' p t' s'3' cur t'' s'4' ptv t'3'. _` drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
  >~ [`eval_expr cx e s'' = (INR ex,fin)`] >-
    (qpat_x_assum `lookup_storage _ (get_storage cx s'' _) = _`
       (SUBST1_TAC o SYM) >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  rename1 `eval_expr cx e s'' = (INL tv,se)` >>
  `lookup_storage (n2w q) (get_storage cx se tr) =
   lookup_storage (n2w q) (get_storage cx s'' tr)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  rpt (qpat_x_assum `!a b c d e'. _` kall_tac) >>
  imp_res_tac read_result_state >>
  gvs[lift_sum_def, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `p` >- run all_tac "aug_storage" >> run all_tac "aug_nonstorage"
) g

| branch prior "aug_storage" g = (
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  fs[vyperTypeInvariantsTheory.eval_result_typed_def] >>
  `value_has_type t cur` by
    (fs[read_place_def] >>
     metis_tac[vyperTypeStatePreservationTheory.read_storage_slot_success_type]) >>
  fs[vyperTypeInvariantsTheory.runtime_place_typed_def,
     place_type_value_def, return_def] >>
  `value_runtime_typed env (expr_type e) v'5'` by
    (drule_all eval_expr_success_storage_facts >> strip_tac >>
     fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `value_has_type t res'` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     metis_tac[vyperTypeBuiltinsTheory.well_typed_binop_success_type]) >>
  gvs[] >>
  drule eval_target_place_storage_mutation_destination >> strip_tac >>
  `((mid',name',keys') <> (mid,name,keys))` by (strip_tac >> gvs[]) >>
  gvs[write_place_def] >>
  Cases_on `type_slot_size ptv = 0`
  >- (drule_all vyperStorageRegionWriteTheory.typed_zero_storage_write_footprint >>
      strip_tac >> gvs[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root' + type_slot_size rtv' <= dimword(:256)` by
    metis_tac[storage_layout_safe_region_nonoverflow] >>
  `w2n (root' + n2w delta) = w2n root' + delta` by
    (`delta < dimword(:256) /\ w2n root' + delta < dimword(:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  rename1 `write_storage_slot cx b _ _ _ se = _` >>
  `lookup_storage (n2w q) (get_storage cx fin tr) =
   lookup_storage (n2w q) (get_storage cx se tr)` by
    (irule declared_capacity_typed_write_frame_result >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >> simp[]
) g

| branch prior "aug_nonstorage" g = (
  prior
  >~ [`write_place cx (MemoryPlace id path) v se = (res,fin)`] >-
    (mp_tac machine_frame_write_memory_place >>
     simp[state_rel_frame_def] >> disch_then (qspec_then `se` mp_tac) >>
     simp[machine_frame_def, get_storage_def] >>
     strip_tac >> Cases_on `tr` >> gvs[get_storage_def]) >>
  gvs[write_place_def, bind_def, get_immutables_def, set_immutable_def,
      lift_option_type_def, lift_sum_def, type_check_def, assert_def,
      return_def, raise_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), get_storage_def] >>
  gvs[get_address_immutables_def, bind_def, return_def, raise_def,
      get_accounts_def, lift_option_type_def, set_address_immutables_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  Cases_on `tr` >> gvs[get_storage_def]
) g

| branch prior "remaining48" g = (
  prior
  >~ [`eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) st = _`]
  >- (qpat_x_assum `~MEM RiskyAcc (accesses_expr _)` mp_tac >>
      simp[accesses_expr_def, risky_call_target_def])
  >~ [`eval_expr cx (Call _ (CreateTarget _ _ _ _) _ _) st = _`]
  >- (qpat_x_assum `~MEM RiskyAcc (accesses_expr _)` mp_tac >>
      simp[accesses_expr_def, risky_call_target_def])
  >~ [`eval_stmt cx (For _ _ _ _ _) st = _`]
  >- run all_tac "stmt_for"
  >> run all_tac "for_cons"
) g

| branch prior "stmt_for" g = (
  fs[int_calls_stmt_def, accesses_stmt_def] >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >> disch_tac >>
  drule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >> disch_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[Once type_stmt_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    metis_tac[vyperTypeExtCallCoreTheory.runtime_consistent_get_tenv] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `evaluate_type (get_tenv cx) typ`
  >- (simp[raise_def]) >> simp[] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (ir,s1)` >> strip_tac >>
  `lookup_storage (n2w q) (get_storage cx s1 tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    (qpat_x_assum `!s'' tyv t. _` mp_tac >>
     simp[lift_option_type_def, return_def] >>
     disch_then irule >> metis_tac[]) >>
  gvs[bind_def, return_def, raise_def] >>
  rename1 `eval_iterator cx it s0 = (INL vs,s2)` >>
  `runtime_consistent env cx s2 /\
   ?tv. evaluate_type env.type_defs typ = SOME tv /\ EVERY (value_has_type tv) vs` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 3 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >> simp[]) >>
  gvs[] >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vs)`
  >- (qpat_x_assum `!s vs t u w. _` mp_tac >>
      simp[check_def, assert_def, return_def] >>
      disch_then (drule_at (Pat `eval_iterator _ _ _ = _`)) >>
      strip_tac >>
      `lookup_storage (n2w q) (get_storage cx fin tr) =
       lookup_storage (n2w q) (get_storage cx s2 tr)` by
       (first_x_assum irule >>
        fs[optionTheory.IS_SOME_EXISTS, bind_def, ignore_bind_def,
           assert_def, return_def, check_def] >> metis_tac[]) >> simp[]) >>
  gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def]
) g

| branch prior "for_cons" g = (
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (lr,sa)` >> strip_tac >>
  `stp.scopes <> []` by simp[Abbr `stp`] >>
  qunabbrev_tac `loop_body` >>
  drule (REWRITE_RULE [ignore_bind_def] for_body_decompose_any) >>
  disch_then (qspecl_then [`cx`, `body'`, `lr`, `sa`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr `stp`] >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tyv v` by fs[] >>
  `env_consistent env cx st` by
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    simp[Abbr `stp`] >> irule push_scope_with_var_env_consistent >>
    metis_tac[]) >>
  `state_well_typed stp` by (
    gvs[Abbr `stp`, vyperTypeExprSoundnessTheory.runtime_consistent_def,
        state_well_typed_def, scope_well_typed_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
  `runtime_consistent (extend_local env id ty F) cx stp` by
    (simp[vyperTypeExprSoundnessTheory.runtime_consistent_def, Abbr `stp`] >>
     qpat_x_assum `runtime_consistent env cx st` mp_tac >>
     simp[vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  `lookup_storage (n2w q) (get_storage cx sa tr) =
   lookup_storage (n2w q) (get_storage cx st tr)` by
    gvs[Abbr `stp`, oneline get_storage_def] >>
  `eval_for cx tyv id body' [v] st =
     ((case lr of INL broke => INL () | INR e => INR e),sa)` by (
    simp[Once evaluate_def, bind_def, ignore_bind_def,
         push_scope_with_var_def, return_def, Abbr `stp`] >>
    qpat_assum `finally _ _ stp = (lr,sa)` (fn th => rewrite_tac[th]) >>
    Cases_on `lr` >> simp[Once evaluate_def, return_def]) >>
  `runtime_consistent env cx sa` by (
    `EVERY (value_has_type tyv) [v]` by simp[] >>
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
    qpat_assum `eval_for _ _ _ _ [v] _ = _`
      (mp_then Any mp_tac (cj 4 eval_scc_type_sound_mutual)) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env'`] mp_tac) >>
    simp[]) >>
  Cases_on `lr` >> gvs[return_def] >>
  Cases_on `x` >> gvs[return_def] >>
  qpat_x_assum `!s'' t s3 t'. _`
    (qspecl_then [`st`, `stp`, `stp`,
                  `st_body with scopes := TL st_body.scopes`] mp_tac) >>
  simp[ignore_bind_def] >>
  disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env'`,
                          `st_body with scopes := TL st_body.scopes`,
                          `res`, `fin`] mp_tac) >>
  simp[] >> disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
) g
| branch prior label g = FAIL_TAC ("Unknown footprint branch: " ^ label) g
and run prior label g =
  (branch prior label g handle e =>
    (print ("Footprint branch: " ^ label ^ "\n");
     print (Parse.term_to_string (#2 g) ^ "\n"); raise e))
and (prior via label) g = run prior label g
  in root end
QED
