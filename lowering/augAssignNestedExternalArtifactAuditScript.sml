(* Reconstruct callable signatures from the actual External program. *)
Theory augAssignNestedExternalArtifactAudit
Ancestors augAssignNestedExternalApplicability augAssignNestedExternalCallerProbe
  augAssignNestedNormalizedProbe vyperTypeContract vyperTypeSystem
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_external_artifact_exists:
  IS_SOME (check_contract F nested_external_cx.layouts 0w
    [(NONE,nested_external_tops)])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``]) >>
  simp[vyperTypeSystemTheory.subscript_vtype_def,
    SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``]) >> simp[]
QED

Definition nested_external_artifact_def:
  nested_external_artifact = THE (check_contract F nested_external_cx.layouts 0w
    [(NONE,nested_external_tops)])
End

Theorem nested_external_artifact_checked:
  check_contract F nested_external_cx.layouts 0w
    [(NONE,nested_external_tops)] = SOME nested_external_artifact
Proof
  mp_tac nested_external_artifact_exists >>
  Cases_on `check_contract F nested_external_cx.layouts 0w
    [(NONE,nested_external_tops)]` >> simp[nested_external_artifact_def]
QED

Definition nested_external_artifact_env_def:
  nested_external_artifact_env = function_entry_env nested_external_artifact
    [(NONE,nested_external_tops)] NONE External []
End

Theorem nested_external_artifact_normal:
  nested_external_artifact = live_artifact nested_external_cx.layouts 0w
    [(NONE,nested_external_tops)]
    (live_functions nested_external_cx.layouts 0w [(NONE,nested_external_tops)])
    (build_contract_type_artifact F [(NONE,nested_external_tops)])
Proof
  mp_tac nested_external_artifact_checked >>
  simp[check_contract_def] >> rpt strip_tac >> gvs[]
QED

Theorem nested_external_artifact_env_normal:
  nested_external_artifact_env = nested_premise_env
Proof
  rewrite_tac[nested_external_artifact_env_def, nested_external_artifact_normal] >>
  EVAL_TAC >> simp[finite_mapTheory.DRESTRICT_FUPDATE] >> EVAL_TAC
QED

Theorem nested_external_artifact_signatures:
  fn_sigs_consistent nested_external_artifact_env.fn_sigs nested_external_cx
Proof
  rewrite_tac[vyperTypeInvariantsTheory.fn_sigs_consistent_def,
    nested_external_artifact_env_normal] >>
  EVAL_TAC >> rpt gen_tac >> strip_tac >> gvs[] >>
  EVAL_TAC >> simp[vyperInterpreterTheory.lookup_function_def]
QED

Theorem nested_external_artifact_stmt_typed:
  type_stmt nested_external_artifact_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_external_artifact_env
Proof
  rewrite_tac[nested_external_artifact_env_normal] >>
  EVAL_TAC >> simp[vyperTypeSystemTheory.subscript_vtype_def] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def]
QED

Theorem nested_external_artifact_context:
  env_context_consistent nested_external_artifact_env nested_external_cx
Proof
  rewrite_tac[nested_external_artifact_env_normal] >>
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> EVAL_TAC >> simp[vyperInterpreterTheory.lookup_function_def]
QED

Theorem nested_external_artifact_basic:
  env_consistent nested_external_artifact_env nested_external_cx nested_premise_es /\
  state_well_typed nested_premise_es /\
  accounts_well_typed nested_premise_es.accounts /\
  context_well_typed nested_external_cx
Proof
  conj_tac >- (simp[vyperTypeInvariantsTheory.env_consistent_def,
      nested_external_artifact_context, nested_external_artifact_env_normal] >>
      EVAL_TAC >> simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  simp[augAssignNestedPremiseProbeTheory.nested_premise_initial_basic] >> EVAL_TAC >> simp[]
QED

Theorem nested_external_artifact_functions:
  functions_well_typed nested_external_cx
Proof
  assume_tac nested_external_artifact_checked >>
  drule vyperTypeContractFunctionTheory.check_contract_functions_well_typed_initial >>
  disch_then (qspecl_then [`nested_external_cx.txn`, `NONE`,
    `nested_external_cx.sources`] mp_tac) >>
  impl_tac >- EVAL_TAC >>
  `initial_evaluation_context nested_external_cx.sources
    nested_external_cx.layouts nested_external_cx.txn NONE = nested_external_cx`
    by EVAL_TAC >> simp[]
QED

Theorem nested_external_storage_observations:
  (!mid n. storage_var_info nested_external_cx mid n =
           storage_var_info nested_initial_cx mid n) /\
  (!mid n subs. declared_storage_region nested_external_cx mid n subs =
                declared_storage_region nested_initial_cx mid n subs) /\
  (!b es. get_storage_backend nested_external_cx b es =
          get_storage_backend nested_initial_cx b es)
Proof
  conj_tac
  >- (rpt gen_tac >> Cases_on `mid = NONE` >>
      EVAL_TAC >> simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `mid = NONE` >>
      EVAL_TAC >> simp[vyperStateTheory.find_var_decl_by_name_def]) >>
  Cases >> EVAL_TAC >> simp[]
QED

Theorem nested_external_storage_wf:
  contract_storage_well_formed nested_external_cx nested_premise_es
Proof
  mp_tac augAssignNestedPremiseProbeTheory.nested_initial_storage_wf >>
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
    vyperLookupStorageTheory.well_formed_storage_def,
    vyperLookupStorageTheory.storage_var_in_range_def,
    nested_external_storage_observations]
QED

Theorem nested_external_layout_safe:
  storage_layout_safe nested_external_cx
Proof
  EVAL_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[vyperStateTheory.find_var_decl_by_name_def, AllCaseEqs()] >>
  gvs[GSYM augAssignNestedReachProbeTheory.nested_reach_outer_ty_def,
      GSYM augAssignNestedReachProbeTheory.nested_reach_inner_ty_def,
      GSYM augAssignNestedReachProbeTheory.nested_reach_fixed_ty_def,
      augAssignNestedPremiseProbeTheory.nested_initial_type_value] >> EVAL_TAC >> simp[]
QED

Theorem nested_external_artifact_expr_inv:
  expr_sim_inv nested_external_slice_cenv nested_external_cx
    nested_external_artifact_env nested_premise_es
Proof
  rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  simp[nested_external_artifact_basic, nested_external_artifact_functions,
       nested_external_storage_wf, nested_external_layout_safe] >>
  `get_tenv nested_external_cx = FEMPTY` by EVAL_TAC >>
  `!fname tys. nested_external_slice_cenv.ce_method_id fname tys =
     w2n (calldata_method_id
       (function_selector fname (vyper_to_abi_types (get_tenv nested_external_cx) tys)))`
    by simp[augAssignNestedExternalEntryProbeTheory.nested_external_slice_cenv_def,
            nested_external_compile_env] >>
  simp[] >>
  simp[augAssignNestedExternalEntryProbeTheory.nested_external_slice_cenv_def,
       nested_external_compile_env, nested_external_artifact_env_normal] >>
  rpt conj_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``]) >>
  simp[compileEnvTheory.nsid_to_string_def, vyperStateTheory.lookup_flag_def,
       vyperStateTheory.find_var_decl_by_name_def]
QED
