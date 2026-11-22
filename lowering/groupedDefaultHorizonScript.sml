Theory groupedDefaultHorizon
Ancestors
  exprLoweringProps loweringStateRelDefs bodyPtrDefs sourceUnitExecution
  vyperStorageFootprint vyperTypeContractStaticMaps vyperTypeContract vyperState
  vyperInterpreter vyperContext vyperStatePreservation vyperPlaceFrames
  whitelistCheckerConsts constSubst list finite_map alist

Theorem grouped_default_empty_regions_horizon:
  storage_trace_regions obs = [] /\ storage_trace_locks obs = [] ==>
  valid_horizon cx st ([],[]) obs
Proof
  Induct_on `obs` >>
  simp[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def,
    storage_trace_locks_def, storage_roots_fit_def, storage_trace_backends_well_formed_def,
    regions_consistent_def, storage_locks_separated_def, storage_well_formed_on_def] >>
  Cases_on `h` >>
  fs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def,
    storage_trace_locks_def, storage_roots_fit_def, storage_trace_backends_well_formed_def,
    regions_consistent_def, storage_locks_separated_def, storage_well_formed_on_def]
QED

Theorem storage_agree_empty_mask[local]:
  storage_agree (storage_dead ([],[]) tr s1) s1 s2 ==>
  storage_agree (storage_dead H tr s1) s1 s2
Proof
  simp[storage_agree_def, storage_dead_def] >> metis_tac[]
QED

Theorem grouped_default_empty_mask_state:
  stmt_state_rel ([],[]) ctx fn ce cx es s ==> stmt_state_rel H ctx fn ce cx es s
Proof
  strip_tac >>
  fs[stmt_state_rel_def, state_rel_def] >>
  rpt conj_tac
  >- (fs[storage_rel_def] >> metis_tac[storage_agree_empty_mask])
  >- (fs[transient_rel_def] >> metis_tac[storage_agree_empty_mask])
  >- (fs[accounts_rel_def, accounts_agree_def, transient_agree_def] >>
      metis_tac[storage_agree_empty_mask]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `LIST_REL (request_agree ([],[]) _) _ _` mp_tac >>
  match_mp_tac LIST_REL_mono >>
  simp[request_agree_def, accounts_agree_def, transient_agree_def] >>
  metis_tac[storage_agree_empty_mask]
QED

Theorem grouped_default_empty_mask_ghost:
  ghost_inv_at (cx_dead ([],[]) cx) 0 NONE ce cx es G tn s ==>
  ghost_inv H NONE ce cx es G tn s
Proof
  simp[ghost_inv_cx_dead, ghost_inv_at_def, stor_taint_ok_at_def, cx_dead_def,
    storage_dead_def] >>
  strip_tac >> first_assum irule >> simp[]
QED

Theorem source_no_sha256_after_const_substitution:
  (!env e. no_sha256_expr (subst_consts_expr env e) ==> no_sha256_expr e) /\
  (!env bt. no_sha256_btarget (subst_consts_btarget env bt) ==> no_sha256_btarget bt) /\
  (!env es. no_sha256_exprs (subst_consts_exprs env es) ==> no_sha256_exprs es) /\
  (!env opt. no_sha256_opt (subst_consts_opt env opt) ==> no_sha256_opt opt) /\
  (!env fs. no_sha256_fields (subst_consts_fields env fs) ==> no_sha256_fields fs)
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, no_sha256_expr_def] >> metis_tac[]
QED

Theorem grouped_default_top_level_lookup_frame:
  (!ts. get_module_code cx src = SOME ts ==> find_var_decl_by_name id ts = NONE) /\
  lookup_global cx src id es = (r,ee) ==>
  ee = es /\ (!v. r = INL v ==> v = PlaceR (ImmutablePlace src id []))
Proof
  strip_tac >> Cases_on `get_module_code cx src` >> fs[] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [lookup_global_def, LET_THM, bind_def, get_immutables_def,
    get_address_immutables_def, lift_option_type_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  metis_tac[sumTheory.INL_11, sumTheory.sum_distinct]
QED

Theorem grouped_default_select_frame:
  (!tr slot kt vt. v <> HashMapRef tr slot kt vt) /\
  select_result cx ty v sb es = (r,ee) ==>
  ee = es /\ (!tr slot kt vt. r <> INL (HashMapRef tr slot kt vt))
Proof
  Cases_on `v`
  >- (simp[select_result_def, bind_def, lift_option_type_def,
        lift_sum_def, return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      metis_tac[sumTheory.INL_11, sumTheory.sum_distinct, eval_result_distinct])
  >- (simp[select_result_def] >> strip_tac >>
      imp_res_tac extend_place_PlaceR_state >> simp[] >>
      Cases_on `p` >> fs[extend_place_def, bind_def, ignore_bind_def, lift_sum_def,
        return_def, raise_def, AllCaseEqs()] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      metis_tac[sumTheory.INL_11, sumTheory.sum_distinct, eval_result_distinct]) >>
  simp[]
QED

Theorem grouped_default_conditional_no_mapping[local]:
  conditional_result cx v st = (r,t) ==> !tr slot kt vt. r <> INL (HashMapRef tr slot kt vt)
Proof
  Cases_on `v` >> simp[conditional_result_def, bind_def, return_def, raise_def]
  >- metis_tac[sumTheory.INL_11, eval_result_distinct] >>
  Cases_on `place_type_value cx p st` >> Cases_on `q` >>
  gvs[bind_def, return_def]
  >- (IF_CASES_TAC >> gvs[return_def]
      >- metis_tac[sumTheory.INL_11, eval_result_distinct] >>
      Cases_on `read_place cx p r'` >> Cases_on `q` >>
      rpt strip_tac >> gvs[bind_def, return_def]) >>
  rpt strip_tac >> gvs[sumTheory.sum_distinct]
QED

Theorem grouped_default_eval_source_frame:
  (!src id ts. ALOOKUP mods src = SOME ts /\
    (declared_constant mods src id \/ declared_immutable mods src id) ==>
    find_var_decl_by_name id ts = NONE) ==>
  ((!cx e. !es r ee.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
      runtime_constant_expr mods e /\ no_sha256_expr e /\ eval_expr cx e es = (r,ee) ==>
    ee with gas_obs := [] = es with gas_obs := [] /\
    !tr slot kt vt. r <> INL (HashMapRef tr slot kt vt)) /\
  (!cx es. !st r ee.
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
      EVERY (runtime_constant_expr mods) es /\ no_sha256_exprs es /\
    eval_exprs cx es st = (r,ee) ==>
    ee with gas_obs := [] = st with gas_obs := []))
Proof
  strip_tac >>
  qsuff_tac
   `(!cx:evaluation_context. !s:stmt. T) /\
    (!cx:evaluation_context. !ss:stmt list. T) /\
    (!cx:evaluation_context. !it:iterator. T) /\
    (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:eval_result list. T) /\
    (!cx e. !es r ee.
      ALOOKUP cx.sources cx.txn.target = SOME mods /\
      runtime_constant_expr mods e /\ no_sha256_expr e /\ eval_expr cx e es = (r,ee) ==>
      ee with gas_obs := [] = es with gas_obs := [] /\
      !tr slot kt vt. r <> INL (HashMapRef tr slot kt vt)) /\
    (!cx es. !st r ee.
      ALOOKUP cx.sources cx.txn.target = SOME mods /\
      EVERY (runtime_constant_expr mods) es /\ no_sha256_exprs es /\
      eval_exprs cx es st = (r,ee) ==>
      ee with gas_obs := [] = st with gas_obs := []) /\
    (!cx:evaluation_context. !bt:base_assignment_target. T) /\
    (!cx:evaluation_context. !bt:base_assignment_target. T) /\
    (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
    (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T)`
  >- simp[] >>
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[runtime_constant_expr_def, no_sha256_expr_def, no_sha256_collections]
  >- suspend "top"
  >- suspend "ifexp"
  >- simp[evaluate_def, return_def]
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- simp[evaluate_def, return_def]
  >- suspend "cons"
QED

Resume grouped_default_eval_source_frame[top]:
  rpt gen_tac >> strip_tac >>
  `get_module_code cx src_id_opt = ALOOKUP mods src_id_opt` by
    (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods`
       (simp_tac (srw_ss()) o cons get_module_code_def o single)) >>
  `!ts. get_module_code cx src_id_opt = SOME ts ==> find_var_decl_by_name id ts = NONE` by
    metis_tac[] >>
  qpat_assum `eval_expr _ _ _ = _`
    (assume_tac o ONCE_REWRITE_RULE[evaluate_def]) >>
  drule_all grouped_default_top_level_lookup_frame >>
  strip_tac >> asm_rewrite_tac[] >>
  metis_tac[eval_result_distinct]
QED

Resume grouped_default_eval_source_frame[ifexp]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >>
  imp_res_tac grouped_default_conditional_no_mapping >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
  metis_tac[evaluation_state_component_equality]
QED

Resume grouped_default_eval_source_frame[struct]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, no_sha256_collections, listTheory.EVERY_MAP] >>
  metis_tac[]
QED

Resume grouped_default_eval_source_frame[subscript]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  Cases_on `subscript_reads_base cx e e'` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[grouped_default_select_frame, eval_result_distinct]
QED

Resume grouped_default_eval_source_frame[attribute]:
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  metis_tac[grouped_default_select_frame]
QED

Resume grouped_default_eval_source_frame[builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Len` >- suspend "length" >>
  Cases_on `bt = Env MsgGas` >- suspend "gas" >>
  suspend "ordinary"
QED

Resume grouped_default_eval_source_frame[length]:
  gvs[] >> rpt strip_tac >>
  qpat_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[return_def] >>
  imp_res_tac result_array_length_state >>
  Cases_on `es` >> gvs[builtin_args_length_ok_def, type_check_def, assert_def, return_def] >>
  metis_tac[constant_expr_runtime_constant, eval_result_distinct, sumTheory.INL_11]
QED

Resume grouped_default_eval_source_frame[gas]:
  gvs[] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
      return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac next_gas_reading_state >> gvs[]
QED

Resume grouped_default_eval_source_frame[ordinary]:
  rpt strip_tac >>
  `!ct addr. code_slice_source bt es <> SOME (ct,addr)` by
    (simp[code_slice_source_SOME] >> rpt strip_tac >>
     gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
  `~precompile_builtin bt` by
    (Cases_on `bt` >> gvs[runtime_constant_builtin_def, constant_builtin_def]) >>
  `EVERY (runtime_constant_expr mods) es` by
    (gvs[EVERY_MEM] >> metis_tac[constant_expr_runtime_constant]) >>
  `code_slice_source bt es = NONE` by
    (Cases_on `code_slice_source bt es` >> simp[] >> PairCases_on `x` >> gvs[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[get_accounts_def, precompile_call_success_def,
    bind_def, return_def, raise_def, AllCaseEqs(), type_check_def, assert_def] >>
  Cases_on `is_self_codesize bt es` >> fs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  metis_tac[]
QED

Resume grouped_default_eval_source_frame[typebuiltin]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED

Resume grouped_default_eval_source_frame[cons]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Finalise grouped_default_eval_source_frame

Theorem grouped_checked_default_source_frame:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  EVERY (runtime_constant_expr [(NONE,tops)]) es /\ no_sha256_exprs es /\
  eval_exprs cx es st = (r,ee) ==>
  ee with gas_obs := [] = st with gas_obs := []
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[check_contract_runtime_namespaces,
      contract_namespaces_ok_module_toplevel_vtype_keys, MEM] >>
  `!src:num option. !id ts. ALOOKUP [(NONE,tops)] src = SOME ts /\
    (declared_constant [(NONE,tops)] src id \/ declared_immutable [(NONE,tops)] src id) ==>
    find_var_decl_by_name id ts = NONE` by
    (simp[declared_constant_def, declared_immutable_def, ALOOKUP_def] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[find_var_decl_by_name_NONE_Immutable, find_var_decl_by_name_NONE_Constant]) >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`] (SPEC_ALL grouped_default_eval_source_frame)) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`cx`,`es`,`st`,`r`,`ee`] mp_tac o CONJUNCT2) >>
  simp[]
QED
