(* Frozen-premise audit for the nested replacement candidate. *)
Theory augAssignNestedPremiseProbe
Ancestors
  augAssignNestedCompileProbe augAssignNestedReachProbe bodySim vyperTypeInvariants
  vyperTypeSystem vyperTypeContract vyperTypeContractFunction vyperInterpreter
  vyperContext vyperState
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_diagnostic_env_excluded:
  ~env_context_consistent nested_reach_env cx
Proof
  simp[env_context_consistent_def, nested_reach_env_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Definition nested_premise_env_def:
  nested_premise_env = nested_reach_env with
    <|bare_global_assignable := FEMPTY;
      toplevel_vtypes := FEMPTY |+ ((NONE,"a"), Type nested_reach_outer_ty)|>
End

Theorem nested_premise_typing:
  type_stmt nested_premise_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_premise_env /\
  type_stmts nested_premise_env (BaseT (UintT 256)) nested_reach_body =
    SOME nested_premise_env
Proof
  EVAL_TAC >> simp[subscript_vtype_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def]
QED

Theorem nested_premise_context:
  env_context_consistent nested_premise_env nested_reach_cx
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[]
QED

Theorem nested_premise_supported_program:
  supported_program nested_reach_tops
Proof
  EVAL_TAC
QED

Definition nested_premise_policy_def:
  nested_premise_policy = <|rpol_target := K T;
    rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize|>
End

Theorem nested_premise_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit nested_reach_tops nested_premise_policy)
Proof
  simp[compileVyperTheory.lower_vyper_runtime_unit_def,
       nested_reach_tops_def] >> EVAL_TAC
QED

Definition nested_premise_unit_def:
  nested_premise_unit = THE
    (lower_vyper_runtime_unit nested_reach_tops nested_premise_policy)
End

Definition nested_premise_cenv_def:
  nested_premise_cenv = nested_compile_env with ce_target := K T
End

Theorem nested_premise_body_inv:
  body_inv nested_reach_tops nested_premise_unit.cu_context
    nested_premise_cenv nested_reach_cx
Proof
  rewrite_tac[body_inv_def] >>
  conj_tac >- ACCEPT_TAC nested_premise_supported_program >>
  conj_tac
  >- (qexistsl [`nested_premise_policy`, `nested_premise_unit`] >>
      simp[nested_premise_cenv_def, nested_premise_unit_def] >>
      mp_tac nested_premise_lowering_exists >>
      Cases_on `lower_vyper_runtime_unit nested_reach_tops nested_premise_policy` >>
      simp[] >> EVAL_TAC) >>
  simp[nested_premise_cenv_def, nested_compile_env_def,
       compileVyperTheory.build_compile_env_def, cenv_module_pins_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem nested_diagnostic_state_excluded:
  ~expr_sim_inv cenv cx env nested_reach_es
Proof
  simp[exprSimHypsDefsTheory.expr_sim_inv_def] >> EVAL_TAC
QED

Definition nested_premise_es_def:
  nested_premise_es = nested_reach_es with <|outcomes := SOME []; scopes := [FEMPTY]|>
End

Theorem nested_premise_initial_basic:
  env_consistent nested_premise_env nested_reach_cx nested_premise_es /\
  state_well_typed nested_premise_es /\
  accounts_well_typed nested_premise_es.accounts /\
  context_well_typed nested_reach_cx
Proof
  conj_tac >- (simp[env_consistent_def, nested_premise_context] >> EVAL_TAC >>
      simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> gen_tac >> Cases_on `addr = 0w` >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Theorem nested_premise_contract_checked:
  IS_SOME (check_contract F nested_reach_cx.layouts 0w
    [(NONE,nested_reach_tops)])
Proof
  EVAL_TAC >> simp[subscript_vtype_def,
    SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED


Definition nested_initial_cx_def:
  nested_initial_cx = initial_evaluation_context nested_reach_cx.sources
    nested_reach_cx.layouts nested_reach_cx.txn NONE
End

Theorem nested_initial_functions:
  functions_well_typed nested_initial_cx
Proof
  mp_tac nested_premise_contract_checked >>
  Cases_on `check_contract F nested_reach_cx.layouts 0w
    [(NONE,nested_reach_tops)]` >> simp[] >>
  drule check_contract_functions_well_typed_initial >>
  disch_then (qspecl_then [`nested_reach_cx.txn`, `NONE`,
    `nested_reach_cx.sources`] mp_tac) >>
  simp[GSYM nested_initial_cx_def] >>
  impl_tac >- EVAL_TAC >> simp[]
QED

Theorem nested_initial_cx_normal:
  nested_initial_cx = nested_reach_cx with
    stk := [(NONE,nested_reach_cx.txn.function_name)]
Proof
  EVAL_TAC
QED

Theorem nested_initial_source_subtraction:
  ?post.
    eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))) nested_premise_es =
      (INL (),post) /\
    lookup_storage 2w (get_storage nested_initial_cx post F) = 6w /\
    lookup_storage 1w (get_storage nested_initial_cx post F) = 0w
Proof
  `7 - 1 = (6:int)` by intLib.COOPER_TAC >>
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[return_def, get_place_def, combinTheory.APPLY_UPDATE_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem nested_initial_body_inv:
  body_inv nested_reach_tops nested_premise_unit.cu_context
    nested_premise_cenv nested_initial_cx
Proof
  rewrite_tac[body_inv_def] >>
  conj_tac >- ACCEPT_TAC nested_premise_supported_program >>
  conj_tac
  >- (qexistsl [`nested_premise_policy`, `nested_premise_unit`] >>
      simp[nested_premise_cenv_def, nested_premise_unit_def] >>
      mp_tac nested_premise_lowering_exists >>
      Cases_on `lower_vyper_runtime_unit nested_reach_tops nested_premise_policy` >>
      simp[] >> EVAL_TAC) >>
  simp[nested_premise_cenv_def, nested_compile_env_def,
       compileVyperTheory.build_compile_env_def, cenv_module_pins_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem nested_initial_context:
  env_context_consistent nested_premise_env nested_initial_cx
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[]
QED

Theorem nested_initial_basic:
  env_consistent nested_premise_env nested_initial_cx nested_premise_es /\
  state_well_typed nested_premise_es /\
  accounts_well_typed nested_premise_es.accounts /\
  context_well_typed nested_initial_cx
Proof
  conj_tac >- (simp[env_consistent_def, nested_initial_context] >> EVAL_TAC >>
      simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  simp[nested_premise_initial_basic] >> EVAL_TAC >> simp[]
QED

Theorem nested_initial_type_value:
  evaluate_type FEMPTY nested_reach_outer_ty =
    SOME (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1))
Proof
  EVAL_TAC
QED

Theorem nested_initial_backend:
  get_storage_backend nested_initial_cx F nested_premise_es =
    (INL (\k:bytes32. if k = 0w then 1w else if k = 1w then 1w
      else if k = 2w then 7w else 0w), nested_premise_es)
Proof
  EVAL_TAC
QED

Theorem nested_initial_slots:
  slots_in_range
    (\k:bytes32. if k = 0w then 1w else if k = 1w then 1w
      else if k = 2w then 7w else 0w) 0
    (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def]
QED

Theorem nested_initial_decl:
  get_module_code nested_initial_cx mid = SOME code /\
  find_var_decl_by_name n code = SOME (decl,id) ==>
  mid = NONE /\ n = "a" /\ id = "a" /\
  decl = StorageVarDecl F nested_reach_outer_ty
Proof
  EVAL_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[find_var_decl_by_name_def, nested_reach_outer_ty_def,
      nested_reach_inner_ty_def, nested_reach_fixed_ty_def, AllCaseEqs()] >>
  EVAL_TAC >> simp[]
QED

Theorem nested_initial_region:
  declared_storage_region nested_initial_cx mid n subs = SOME (b,slot,tv) ==>
  mid = NONE /\ n = "a" /\ subs = [] /\ b = F /\ slot = 0w /\
  tv = ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1)
Proof
  strip_tac >> drule vyperStorageLayoutSafetyTheory.declared_storage_region_backend >>
  strip_tac >> drule_all nested_initial_decl >> strip_tac >> gvs[] >>
  `declared_storage_region nested_initial_cx NONE "a" [] =
    SOME (F,0w,ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1))` by EVAL_TAC >>
  gvs[]
QED

Theorem nested_initial_var_info:
  storage_var_info nested_initial_cx mid n = SOME (b,off,tv) ==>
  mid = NONE /\ n = "a" /\ b = F /\ off = 0 /\
  tv = ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1)
Proof
  simp[vyperLookupStorageTheory.storage_var_info_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all nested_initial_decl >> strip_tac >> gvs[] >>
  `lookup_var_slot_from_layout nested_initial_cx F NONE "a" = SOME 0` by EVAL_TAC >>
  `get_tenv nested_initial_cx = FEMPTY` by EVAL_TAC >>
  gvs[nested_initial_type_value]
QED

Theorem nested_initial_storage_wf:
  contract_storage_well_formed nested_initial_cx nested_premise_es
Proof
  rewrite_tac[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def] >>
  conj_tac
  >- (rewrite_tac[vyperLookupStorageTheory.well_formed_storage_def,
        vyperLookupStorageTheory.storage_var_in_range_def] >>
      rpt strip_tac >> drule nested_initial_var_info >> strip_tac >>
      gvs[nested_initial_backend] >> ACCEPT_TAC nested_initial_slots) >>
  rpt strip_tac >> drule nested_initial_region >> strip_tac >>
  gvs[nested_initial_backend] >> ACCEPT_TAC nested_initial_slots
QED

Theorem nested_initial_layout_safe:
  storage_layout_safe nested_initial_cx
Proof
  EVAL_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[find_var_decl_by_name_def, AllCaseEqs()] >>
  gvs[GSYM nested_reach_outer_ty_def, GSYM nested_reach_inner_ty_def,
      GSYM nested_reach_fixed_ty_def, nested_initial_type_value] >> EVAL_TAC >> simp[]
QED
