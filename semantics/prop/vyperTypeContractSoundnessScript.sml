(*
 * Final checked-contract type-soundness theorems.
 *
 * This theory owns the public transaction/runtime-readiness predicates and the
 * final deployment/readiness and checked external-call no-TypeError theorems.
 *)

Theory vyperTypeContractSoundness
Ancestors
  list rich_list arithmetic finite_map alist option pair
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPureExpr
  vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperExprNoControl vyperTypeEvalSoundness vyperTypeCallGraph
  vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeContractFunction vyperTypeContractGetter vyperTypeEntryReadiness
  vyperTypeStatePreservation vyperTypeConstantFold vyperTypeExternalDefaults
  vyperTypeConstantCells
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Public transaction and runtime-readiness predicates ===== *)

Definition call_tx_well_typed_def:
  call_tx_well_typed tx <=>
    LENGTH tx.calldata < 2 ** 256 /\
    tx.value < 2 ** 256 /\
    tx.time_stamp < 2 ** 256 /\
    tx.block_number < 2 ** 256 /\
    tx.blob_base_fee < 2 ** 256 /\
    tx.gas_price < 2 ** 256 /\
    tx.chain_id < 2 ** 256 /\
    tx.gas_limit < 2 ** 256 /\
    tx.base_fee < 2 ** 256 /\
    tx.prev_randao < 2 ** 256
End

(* ===== Checked constant initializers ===== *)

Theorem constant_expr_pure:
  !mods e. constant_expr mods e ==> pure_expr e
Proof
  ho_match_mp_tac constant_expr_ind >>
  rw[constant_expr_def, pure_expr_def] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem checked_constant_initializer_pure:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tls /\
  MEM (VariableDecl vis (Constant e) id ty init) tls ==>
  pure_expr e
Proof
  strip_tac >>
  drule_all check_contract_toplevel_decl_MEM >>
  simp[check_toplevel_decl_def] >>
  metis_tac[constant_expr_pure]
QED

Theorem checked_constant_initializer_eval_pure:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tls /\
  MEM (VariableDecl vis (Constant e) id ty init) tls /\
  eval_expr cx e st = (INL v,st') ==>
  eval_pure_expr cx st e = SOME v
Proof
  metis_tac[checked_constant_initializer_pure,
            eval_expr_to_eval_pure_expr_some]
QED

Theorem call_tx_well_typed_empty_zero_witness:
  ?tx. tx.args = [] /\ tx.value = 0 /\ call_tx_well_typed tx
Proof
  qexists `empty_call_txn` >>
  simp[empty_call_txn_def, call_tx_well_typed_def]
QED

Theorem call_tx_well_typed_initial_context[local]:
  call_tx_well_typed tx ==>
  context_well_typed (initial_evaluation_context sources layouts tx src)
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_tx_well_typed_initial_context_stk[local]:
  call_tx_well_typed tx ==>
  context_well_typed
    ((initial_evaluation_context sources layouts tx src) with stk := [(src,fn)])
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_external_args_defaults_bind_typed[local]:
  bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME scope /\
  LIST_REL
    (\v arg. ?tv. evaluate_type (type_env_all_modules all_mods) (SND arg) = SOME tv /\
                   value_has_type tv v)
    (vals ++ dflt_vs) args ==>
  args_values_typed (type_env_all_modules all_mods) args (vals ++ dflt_vs)
Proof
  rw[args_values_typed_def]
  >- (imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_APPEND] >> decide_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >>
  strip_tac >>
  first_x_assum drule >>
  simp[]
QED

(* The exports of tx.target name only functions of allocated modules
   (exports_ok); check_contract checks only the live functions. *)
Definition checked_contract_runtime_ready_def:
  checked_contract_runtime_ready art mods am tx <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    exports_ok am.layouts tx.target mods
      (case ALOOKUP am.exports tx.target of NONE => [] | SOME exps => exps) /\
    immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
      (initial_evaluation_context am.sources am.layouts tx NONE)
      am.immutables
End

(* The module call_external selects is allocated. *)
Theorem checked_contract_runtime_ready_module_allocated:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  ALOOKUP mods (find_function_module am tx.target fn) = SOME ts ==>
  module_allocated am.layouts tx.target (find_function_module am tx.target fn) ts
Proof
  rw[checked_contract_runtime_ready_def, find_function_module_def] >>
  Cases_on `ALOOKUP am.exports tx.target` >> gvs[]
  >- metis_tac[check_contract_main_module_allocated] >>
  rename1 `ALOOKUP am.exports tx.target = SOME exps` >>
  Cases_on `ALOOKUP exps fn` >> gvs[]
  >- metis_tac[check_contract_main_module_allocated] >>
  gvs[exports_ok_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem checked_contract_initial_context_functions_follow_call_graph[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods ==>
  functions_follow_call_graph (contract_call_edges mods)
    (initial_evaluation_context am.sources am.layouts tx src)
Proof
  rw[functions_follow_call_graph_def, initial_evaluation_context_def] >>
  gvs[get_module_code_def] >>
  drule ALOOKUP_MEM >>
  disch_then assume_tac >>
  drule lookup_callable_function_SOME_decompose >>
  strip_tac
  >- simp[function_int_calls_def, int_calls_expr_def, int_calls_stmt_def] >>
  rw[EVERY_MEM, call_edge_rel_def] >>
  irule contract_call_edges_function >>
  metis_tac[]
QED

(* checked_explicit_external_body_call_evaluation_safe is shared with
 * actual-state entry soundness in vyperTypeExternalDefaults. *)

(* checked_call_external_no_type_error is proved near the end of this file,
   after its explicit-function and public-getter branch helpers. *)

(* ===== Deployment establishes runtime immutable readiness ===== *)

Theorem load_contract_success_cases:
  load_contract orc am tx mods exps = INL (am_deployed,rqs) ==>
  ?imms ts mut nr args dflts ret body v am_ctor.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function orc
      (am with <| immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps) |>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE) with in_deploy := T)
      nr mut ts mods args dflts tx.args body ret = (INL v, am_ctor, rqs) /\
    am_deployed = finalize_pending_deletions
      (am_ctor with sources updated_by CONS (tx.target,mods))
Proof
  rw[load_contract_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[] >>
  Cases_on `lookup_function NONE tx.function_name Deploy
              (case ALOOKUP mods NONE of SOME ts => ts | NONE => [])` >> gvs[] >>
  Cases_on `x'` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `call_external_function orc
      (am with <|immutables updated_by CONS (tx.target,x);
                exports updated_by CONS (tx.target,exps)|>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx NONE)
         with in_deploy := T)
      q' q (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods q'' q''' tx.args r q''''` >>
  gvs[] >>
  Cases_on `q'''''` >> gvs[] >>
  rename1 `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = (INL value, machine_requests)` >>
  Cases_on `machine_requests` >> gvs[]
QED

(* A source-level deployment with no matching explicit constructor takes the
   ordinary call path using lookup_function's synthetic constructor, rather
   than the defensive NONE branch of load_contract. *)
Theorem load_contract_success_no_constructor_decl:
  load_contract orc am tx mods exps = INL (am_deployed,rqs) /\
  ~(?fm nr raw args dflts ret body.
      MEM (FunctionDecl Deploy fm nr raw tx.function_name
             args dflts ret body)
        (case ALOOKUP mods NONE of SOME ts => ts | NONE => [])) ==>
  ?imms ts v am_ctor.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (Payable,F,[],[],NoneT,[]) /\
    call_external_function orc
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE) with in_deploy := T)
      F Payable ts mods [] [] tx.args [] NoneT = (INL v,am_ctor,rqs) /\
    am_deployed = finalize_pending_deletions
      (am_ctor with sources updated_by CONS (tx.target,mods))
Proof
  strip_tac >>
  drule lookup_function_Deploy_no_decl >>
  disch_then (qspec_then `NONE` assume_tac) >>
  drule load_contract_success_cases >> strip_tac >>
  gvs[]
QED

Theorem call_external_function_deploy_success_evaluate_all_constants[local]:
  !orc rqs am cx nr mut ts all_mods args dflts vals body ret v am_out.
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) ==>
  ?am_c.
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()]
QED

Theorem deployed_check_contract_bare_globals_consistent[local]:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    ?ts.
      get_module_code
        (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx src) src = SOME ts /\
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      is_bare_global_decl id ts /\
      find_var_decl_by_name id ts = NONE /\
      ty <> NoneT
Proof
  rw[] >>
  drule load_contract_success_cases >>
  strip_tac >> gvs[] >>
  drule check_contract_bare_globals_consistent_initial >>
  simp[] >>
  disch_then (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
  simp[]
QED

Theorem constants_env_preserves_lookup_not_key[local]:
  constants_env cx am addr src ts acc = SOME cenv /\
  ~(MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))) /\
  FLOOKUP acc id = SOME x ==>
  FLOOKUP cenv id = SOME x
Proof
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  Induct_on `ts` >- (rw[constants_env_def] >> gvs[]) >>
  gen_tac >> gen_tac >> Cases_on `h` >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >>
       gvs[constants_env_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  metis_tac[FLOOKUP_UPDATE]
QED


Theorem constants_env_head_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src)
    ((VariableDecl vis (Constant e) id ty init)::ts))) /\
  constants_env cx am addr src
    ((VariableDecl vis (Constant e) id ty init)::ts) acc = SOME cenv ==>
  ?tv v. FLOOKUP cenv id = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs()] >>
  qexists `v` >> simp[] >>
  metis_tac[constants_env_preserves_lookup_not_key, FLOOKUP_UPDATE]
QED
Theorem constants_env_contains_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
  constants_env cx am addr src ts acc = SOME cenv /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  ?tv v. FLOOKUP cenv id = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `init` >> qid_spec_tac `ty` >> qid_spec_tac `id` >>
  qid_spec_tac `e` >> qid_spec_tac `vis` >>
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >> qid_spec_tac `addr` >>
  qid_spec_tac `am` >> qid_spec_tac `cx` >>
  recInduct constants_env_ind >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  metis_tac[constants_env_head_constant_type, constants_env_preserves_lookup_not_key,
            FLOOKUP_UPDATE]
QED

Theorem merge_constants_preserves_lookup_not_source[local]:
  src <> src' /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP (merge_constants addr src' cenv am).immutables addr of
     | SOME m => m
     | NONE => [])) id = SOME x
Proof
  rw[merge_constants_def, get_source_immutables_set_other,
     empty_immutables_def, alistTheory.ALOOKUP_ADELKEY]
QED

Theorem evaluate_module_constants_preserves_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_module_constants cx am addr mods = SOME am_c /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- (rw[evaluate_module_constants_def] >> gvs[]) >>
  gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_module_constants_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum irule >>
  simp[] >>
  qexists `merge_constants addr h0 cenv am` >>
  simp[] >>
  irule merge_constants_preserves_lookup_not_source >>
  simp[]
QED
Theorem evaluate_module_constants_preserves_merged_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_module_constants cx (merge_constants addr src cenv am) addr mods = SOME am_c /\
  FLOOKUP cenv id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  rw[] >>
  drule evaluate_module_constants_preserves_lookup_not_source >>
  disch_then drule >>
  disch_then irule >>
  simp[merge_constants_def, get_source_immutables_set_same,
       empty_immutables_def, FLOOKUP_FUNION]
QED

Theorem evaluate_module_constants_contains_constant_type[local]:
  ALL_DISTINCT (MAP FST mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods) /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_module_constants cx am addr mods = SOME am_c ==>
  ?tv v. FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    id = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >>
  Induct_on `mods` >- rw[evaluate_module_constants_def] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_module_constants_def, alistTheory.ALOOKUP_def] >>
  gvs[AllCaseEqs()] >-
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel h0) h1))` by
       gvs[contract_keys_def, ALL_DISTINCT_APPEND] >>
     drule constants_env_contains_constant_type >>
     disch_then drule >>
     disch_then drule >>
     strip_tac >>
     `FLOOKUP (get_source_immutables h0
        (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
        id = SOME (tv,v)` by
       (gvs[] >>
        drule evaluate_module_constants_preserves_merged_lookup_not_source >>
        disch_then drule >>
        disch_then drule >>
        simp[]) >>
     qexistsl [`tv`,`v`] >>
     gvs[set_current_module_def, get_tenv_def]) >>
  first_x_assum irule >>
  gvs[contract_keys_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem evaluate_all_constants_contains_constant_type[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  ?tv v. FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    id = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rw[evaluate_all_constants_def] >>
  `contract_namespaces_ok F (constants_order mods)` by
    simp[contract_namespaces_ok_constants_order] >>
  `ALOOKUP (constants_order mods) src = SOME ts` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     fs[contract_namespaces_ok_def, MEM_constants_order] >>
     metis_tac[alistTheory.ALOOKUP_MEM]) >>
  gvs[contract_namespaces_ok_def] >>
  drule_all evaluate_module_constants_contains_constant_type >>
  simp[]
QED

Theorem contract_toplevel_vtype_key_MEM_Variable[local]:
  MEM (src,ts) mods /\ MEM (VariableDecl vis mut id ty init) ts ==>
  MEM ((src : num option),id)
    (contract_keys toplevel_vtype_keys_toplevel mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)` >> simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED
Theorem module_immutable_name_type_unique[local]:
  !src ts visI idI tyI initI visJ idJ tyJ initJ.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visJ Immutable idJ tyJ initJ) ts /\
    idJ = idI ==>
    tyJ = tyI
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED


Theorem constants_do_not_clobber_single_immutable[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis Immutable id_str ty init) ts ==>
  constants_do_not_clobber_bare_globals
    mods (FEMPTY |+ ((src,id_str), ty))
Proof
  rw[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE] >>
  gvs[] >>
  CCONTR_TAC >> gvs[] >>
  rename1 `MEM (src,other_ts) mods` >>
  `ALOOKUP mods src = SOME other_ts` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) other_ts))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys,
              alistTheory.ALOOKUP_MEM] >>
  metis_tac[module_immutable_constant_names_distinct]
QED

Theorem deploy_constants_setup_bare_globals_ready:
  check_contract F layouts target mods = SOME call_art /\
  ALOOKUP sources target = SOME mods /\
  tx.target = target /\
  get_tenv cx = type_env_all_modules mods /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  (!src id ty.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
     IS_SOME (FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id)) /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules mods) ty = SOME tv)
Proof
  rw[check_contract_def] >>
  gvs[]
  >- (rw[] >>
      drule build_contract_type_artifact_bare_globals_sound >>
      disch_then drule >>
      strip_tac >>
      gvs[]
      >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) id)` by
            (irule initial_immutables_contains_decl >>
             qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
             simp[] >>
             conj_tac
             >- (irule find_var_decl_by_name_NONE_Immutable >>
                 conj_tac
                 >- (qexists `src` >>
                     irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                     metis_tac[alistTheory.ALOOKUP_MEM]) >>
                 metis_tac[]) >>
             metis_tac[is_immutable_decl_MEM]) >>
          gvs[IS_SOME_EXISTS] >>
          qexists `x` >>
          irule evaluate_all_constants_preserves_bare_global_lookup_type >>
          qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,id),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
          gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
          gvs[] >>
          metis_tac[constants_do_not_clobber_single_immutable]) >>
      gvs[] >>
      drule_all evaluate_all_constants_contains_constant_type >>
      strip_tac >> simp[IS_SOME_EXISTS]) >>
  rw[] >>
  `(?ts vis id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis Immutable id_str ty init) ts /\
      id = id_str) \/
   (?ts vis e id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
      id = id_str)` by
    metis_tac[build_contract_type_artifact_bare_globals_sound] >>
  gvs[]
  >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) id)` by
        (irule initial_immutables_contains_decl >>
         qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
         simp[] >>
         conj_tac
         >- (irule find_var_decl_by_name_NONE_Immutable >>
             conj_tac
             >- (qexists `src` >>
                 irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                 metis_tac[alistTheory.ALOOKUP_MEM]) >>
             metis_tac[]) >>
         metis_tac[is_immutable_decl_MEM]) >>
      gvs[IS_SOME_EXISTS] >>
      `FLOOKUP
         (get_source_immutables src
            (case ALOOKUP am_c.immutables tx.target of NONE => [] | SOME m => m))
         id = SOME x` by
        (irule evaluate_all_constants_preserves_bare_global_lookup_type >>
         qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,id),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
         gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
         metis_tac[constants_do_not_clobber_single_immutable]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
         metis_tac[alistTheory.ALOOKUP_MEM]) >>
      `is_immutable_decl id ts` by
        metis_tac[is_immutable_decl_MEM] >>
      irule initial_immutables_all_bare_global_type >>
      qexistsl [`id`, `imms`, `mods`, `src`, `ts`, `v`] >>
      gvs[] >>
      metis_tac[module_immutable_name_type_unique]) >>
  drule evaluate_all_constants_contains_constant_type >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
  gvs[]
QED

Theorem checked_constant_decl_typed[local]:
  check_contract F layouts target mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  assignable_type (type_env_all_modules mods) ty /\
  well_typed_expr (artifact_env artifact mods src) e /\
  expr_type e = ty
Proof
  rpt strip_tac >>
  drule check_contract_toplevel_decl_MEM >>
  disch_then drule >>
  disch_then drule >>
  simp[check_toplevel_decl_def]
QED




(* TOP-LEVEL: The ordinary freshly initialized immutable table satisfies the
 * pre-constant declaration/tag agreement boundary.
 *
 * WHY THIS IS TRUE:
 * initial_immutables stores evaluated declaration tags for immutables and no
 * constant values.  Checker namespace uniqueness prevents an immutable entry
 * from masquerading as a distinct constant declaration at the same source key.
 * Replacing the target entry discards arbitrary pre-existing target values. *)
Theorem checked_initial_immutables_constants_input_tags_agree:
  check_contract F layouts target mods = SOME artifact /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods
    (am with immutables updated_by CONS (target,imms))
Proof
  rw[deployment_constants_input_tags_agree_def,
     initial_target_immutables_lookup] >>
  qpat_x_assum `check_contract F layouts target mods = SOME artifact` mp_tac >>
  rw[check_contract_def] >>
  gvs[] >>
  drule initial_immutables_lookup_origin >>
  disch_then drule >>
  strip_tac
  >- (`ALOOKUP mods src = SOME ts` by
        (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
         gvs[contract_namespaces_ok_def]) >>
      `ALOOKUP mods src = SOME ts'` by
        (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
         gvs[contract_namespaces_ok_def]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
      metis_tac[module_immutable_name_type_unique]) >>
  `ALOOKUP mods src = SOME ts` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  `ALOOKUP mods src = SOME ts'` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
  metis_tac[module_immutable_constant_names_distinct]
QED


Theorem deployment_constant_cells_typed_initial[local]:
  machine_well_typed am /\
  deployment_constants_input_tags_agree tenv addr mods am ==>
  deployment_constant_cells_typed tenv addr mods am
Proof
  rw[deployment_constant_cells_typed_def]
  >- (gvs[deployment_constants_input_tags_agree_def] >>
      qpat_x_assum `!src ts vis mut id ty init tv v. _`
        (qspecl_then [`src`,`ts`,`vis`,`Constant e`,`id`,`ty`,`init`,`tv`,`v`]
          mp_tac) >>
      simp[]) >>
  Cases_on `ALOOKUP am.immutables addr` >>
  gvs[get_source_immutables_def] >>
  `MEM (addr,x) am.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `imms_well_typed x` by
    (gvs[machine_well_typed_def, listTheory.EVERY_MEM] >>
     qpat_x_assum `!z. MEM z am.immutables ==> _`
       (qspec_then `(addr,x)` mp_tac) >> simp[]) >>
  Cases_on `ALOOKUP x src` >> gvs[get_source_immutables_def] >>
  gvs[imms_well_typed_def] >>
  first_x_assum drule_all >> simp[]
QED


Definition constant_fmap_well_typed_def[local]:
  constant_fmap_well_typed (m : (string, type_value # value) fmap) <=>
    !id tv v. FLOOKUP m id = SOME (tv,v) ==>
      value_has_type tv v /\ well_formed_type_value tv
End

Theorem merge_constants_machine_well_typed[local]:
  machine_well_typed am /\ constant_fmap_well_typed cenv ==>
  machine_well_typed (merge_constants addr src cenv am)
Proof
  strip_tac >>
  qabbrev_tac `old = case ALOOKUP am.immutables addr of
                     | NONE => empty_immutables | SOME m => m` >>
  `imms_well_typed old` by
    (Cases_on `ALOOKUP am.immutables addr` >>
     gvs[Abbr `old`, empty_immutables_def, imms_well_typed_def] >>
     `MEM (addr,x) am.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
     gvs[machine_well_typed_def, listTheory.EVERY_MEM] >>
     first_x_assum drule >> simp[imms_well_typed_def]) >>
  `imms_well_typed
     (set_source_immutables src
       (cenv ⊌ get_source_immutables src old) old)` by
    (simp[imms_well_typed_def, set_source_immutables_def,
          get_source_immutables_def, alistTheory.ALOOKUP_ADELKEY] >>
     rpt gen_tac >> strip_tac >>
     Cases_on `src_id_opt = src` >> gvs[FLOOKUP_FUNION]
     >- (Cases_on `FLOOKUP cenv id`
         >- (gvs[] >> Cases_on `ALOOKUP old src` >>
             gvs[imms_well_typed_def, get_source_immutables_def] >>
             metis_tac[])
         >- (gvs[constant_fmap_well_typed_def] >> metis_tac[])) >>
     gvs[imms_well_typed_def] >> metis_tac[]) >>
  rw[machine_well_typed_def, merge_constants_def, Abbr `old`] >>
  gvs[machine_well_typed_def, listTheory.EVERY_MEM] >>
  rw[] >> PairCases_on `e` >> gvs[alistTheory.MEM_ADELKEY] >>
  first_x_assum drule >> simp[]
QED


Theorem checked_constants_env_output_invariants[local]:
  !work acc cenv.
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP mods src = SOME tls /\
    get_tenv cx = type_env_all_modules mods /\
    context_well_typed cx /\ machine_well_typed am /\
    deployment_constant_cells_typed
      (type_env_all_modules mods) cx.txn.target mods am /\
    contract_namespaces_ok F mods /\ EVERY (λtl. MEM tl tls) work /\
    constant_fmap_well_typed acc /\
    constant_fmap_declared_typed (type_env_all_modules mods) tls acc /\
    constants_env (set_current_module cx src) am cx.txn.target src
      work acc = SOME cenv ==>
    constant_fmap_well_typed cenv /\
    constant_fmap_declared_typed (type_env_all_modules mods) tls cenv
Proof
  Induct_on `work`
  >- simp[constants_env_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h` >> gvs[constants_env_def]
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (Cases_on `v0` >> gvs[constants_env_def]
      >- (fs[set_current_module_def, get_tenv_def] >>
          Cases_on `evaluate_type (type_env_all_modules mods) t` >>
      gvs[AllCaseEqs()] >>
      qmatch_asmsub_rename_tac
        `FST ((do result <- eval_expr _ e; read_result _ result od) _) = INL eval_v` >>
      qmatch_asmsub_rename_tac
        `evaluate_type (type_env_all_modules mods) t = SOME eval_tv` >>
      `?st'. (do result <- eval_expr (set_current_module cx src) e;
                 read_result (set_current_module cx src) result od)
          (initial_state (merge_constants cx.txn.target src acc am) [FEMPTY]) =
          (INL eval_v,st')` by
        (Cases_on `(do result <- eval_expr (set_current_module cx src) e;
                      read_result (set_current_module cx src) result od)
          (initial_state (merge_constants cx.txn.target src acc am) [FEMPTY])` >>
         gvs[set_current_module_def]) >>
      `machine_well_typed
         (merge_constants cx.txn.target src acc am)` by
        metis_tac[merge_constants_machine_well_typed] >>
      `deployment_constant_cells_typed
         (type_env_all_modules mods) cx.txn.target mods
         (merge_constants cx.txn.target src acc am)` by
        (irule merge_constants_preserves_constant_cells_typed >> simp[] >>
         metis_tac[]) >>
      `check_toplevel_decl mods artifact src
         (VariableDecl v (Constant e) s t o')` by
        metis_tac[check_contract_toplevel_decl_MEM] >>
      gvs[check_toplevel_decl_def] >>
      `value_runtime_typed (artifact_env artifact mods src) (expr_type e) eval_v` by
        (irule constant_eval_expr_read_typed >> simp[] >>
         qexistsl [`merge_constants cx.txn.target src acc am`,
           `set_current_module cx src`, `[FEMPTY]`, `st'`] >>
         simp[set_current_module_def] >> metis_tac[]) >>
      `value_has_type eval_tv eval_v` by
        gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def] >>
      `well_formed_type_value eval_tv` by
        metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
      first_x_assum (qspecl_then
        [`acc |+ (s,(eval_tv,eval_v))`,`cenv`] mp_tac) >>
      simp[] >> impl_tac
      >- (conj_tac
          >- (rw[constant_fmap_well_typed_def, FLOOKUP_UPDATE] >>
          Cases_on `id = s` >> gvs[] >>
              metis_tac[constant_fmap_well_typed_def]) >>
          rw[constant_fmap_declared_typed_def, FLOOKUP_UPDATE] >>
          Cases_on `id = s` >> gvs[]
          >- (qexistsl [`v`,`e`,`expr_type e`,`o'`] >> gvs[]) >>
          metis_tac[constant_fmap_declared_typed_def]) >>
      simp[])
      >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
      >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
      >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[]))
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[])
QED

Theorem checked_evaluate_module_constants_preserves_invariants[local]:
  !work am am_c.
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    get_tenv cx = type_env_all_modules mods /\ context_well_typed cx /\
    contract_namespaces_ok F mods /\ EVERY (λm. MEM m mods) work /\
    machine_well_typed am /\
    deployment_constant_cells_typed
      (type_env_all_modules mods) cx.txn.target mods am /\
    evaluate_module_constants cx am cx.txn.target work = SOME am_c ==>
    machine_well_typed am_c /\
    deployment_constant_cells_typed
      (type_env_all_modules mods) cx.txn.target mods am_c
Proof
  Induct_on `work`
  >- simp[evaluate_module_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  gvs[evaluate_module_constants_def, AllCaseEqs()] >>
  `ALOOKUP mods h0 = SOME h1` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  `constant_fmap_well_typed cenv /\
   constant_fmap_declared_typed (type_env_all_modules mods) h1 cenv` by
    (irule checked_constants_env_output_invariants >>
     simp[constant_fmap_well_typed_def,
          constant_fmap_declared_typed_def] >>
     qexistsl [`FEMPTY`,`am`,`artifact`,`cx`,`h0`,`h1`] >>
     simp[listTheory.EVERY_MEM]) >>
  `machine_well_typed
     (merge_constants cx.txn.target h0 cenv am)` by
    metis_tac[merge_constants_machine_well_typed] >>
  `deployment_constant_cells_typed
     (type_env_all_modules mods) cx.txn.target mods
     (merge_constants cx.txn.target h0 cenv am)` by
    (irule merge_constants_preserves_constant_cells_typed >> simp[] >>
     metis_tac[]) >>
  first_x_assum (qspecl_then
    [`merge_constants cx.txn.target h0 cenv am`,`am_c`] mp_tac) >> simp[]
QED

(* TOP-LEVEL: Successful checked whole-contract constant evaluation produces
 * exactly the typed constant environment required by deployment entry.
 *
 * WHY THIS IS TRUE:
 * Successful check_contract supplies namespace uniqueness and types every
 * constant initializer against the artifact environment.  The input-tag
 * agreement premise and machine well-typedness together type any pre-existing
 * bare global at its checked annotation, excluding mismatched-tag machines.
 * Induction through constants_env uses expression type soundness to strengthen
 * each successful INL (Value v) result from its stored runtime tag to
 * value_has_type.  The induction invariant also says that merging the typed
 * accumulator preserves machine well-typedness and input-tag agreement for
 * later constants.  A second induction over evaluate_all_constants transports
 * each module result across the remaining distinct sources.  Runtime contexts
 * need the F checker result; deployment-mode contexts additionally need the T
 * checker result because functions_well_typed follows the context mode.
 * cx.layouts and cx.nonreentrant_slot connect the arbitrary evaluation context
 * to checker/layout authority used by internal-call soundness. *)
Theorem checked_evaluate_all_constants_output_typed:
  check_contract F layouts target mods = SOME artifact /\
  (cx.in_deploy ==>
    ?deploy_art. check_contract T layouts target mods = SOME deploy_art) /\
  cx.layouts = layouts /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot layouts target /\
  get_tenv cx = type_env_all_modules mods /\
  machine_well_typed am /\
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods am /\
  context_well_typed cx /\
  ALOOKUP cx.sources target = SOME mods /\
  cx.txn.target = target /\
  evaluate_all_constants cx am target mods = SOME am_c ==>
  deployment_constants_output_typed
    (type_env_all_modules mods) target mods am_c
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by
    (qpat_x_assum `check_contract F layouts target mods = SOME artifact` mp_tac >>
     simp[check_contract_def] >> metis_tac[]) >>
  `deployment_constant_cells_typed
     (type_env_all_modules mods) target mods am` by
    metis_tac[deployment_constant_cells_typed_initial] >>
  `machine_well_typed am_c /\
   deployment_constant_cells_typed
     (type_env_all_modules mods) target mods am_c` by
    (gvs[evaluate_all_constants_def] >>
     irule checked_evaluate_module_constants_preserves_invariants >>
     simp[listTheory.EVERY_MEM, MEM_constants_order] >>
     qexistsl [`am`,`constants_order mods`] >>
     simp[listTheory.EVERY_MEM, MEM_constants_order]) >>
  rw[deployment_constants_output_typed_def]
  >- gvs[machine_well_typed_def] >>
  `ALOOKUP mods src = SOME ts` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  `?tv v. FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of
          | SOME m => m | NONE => []))
       id = SOME (tv,v) /\
     evaluate_type (get_tenv cx) ty = SOME tv` by
    (irule evaluate_all_constants_contains_constant_type >>
     qexistsl [`am`,`e`,`init`,`mods`,`ts`,`vis`] >>
     simp[] >> metis_tac[]) >>
  qexistsl [`tv`,`v`] >> simp[] >>
  Cases_on `ALOOKUP am_c.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  `MEM (cx.txn.target,x) am_c.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `imms_well_typed x` by
    (gvs[machine_well_typed_def, listTheory.EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  Cases_on `ALOOKUP x src` >> gvs[imms_well_typed_def] >> metis_tac[]
QED

(* TOP-LEVEL: Determinism of evaluate_all_constants packages one typed
 * successful output as checked_deployment_constants_ready. *)
Theorem checked_deployment_constants_ready_from_success:
  check_contract F layouts target mods = SOME artifact /\
  (cx.in_deploy ==>
    ?deploy_art. check_contract T layouts target mods = SOME deploy_art) /\
  cx.layouts = layouts /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot layouts target /\
  get_tenv cx = type_env_all_modules mods /\
  machine_well_typed am /\
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods am /\
  context_well_typed cx /\
  ALOOKUP cx.sources target = SOME mods /\
  cx.txn.target = target /\
  evaluate_all_constants cx am target mods = SOME am_c ==>
  checked_deployment_constants_ready cx am target mods
Proof
  strip_tac >>
  `deployment_constants_output_typed
     (type_env_all_modules mods) target mods am_c` by
    (drule_all checked_evaluate_all_constants_output_typed >> simp[]) >>
  rw[checked_deployment_constants_ready_def] >>
  metis_tac[]
QED

(* TOP-LEVEL: checked_deployment_constants_ready needs no success premise: the
 * checker's constants fold makes evaluate_all_constants succeed from the
 * immutables load_contract installs (check_contract_evaluate_all_constants). *)
Theorem checked_deployment_constants_ready_from_check:
  check_contract F layouts target mods = SOME artifact /\
  (cx.in_deploy ==>
    ?deploy_art. check_contract T layouts target mods = SOME deploy_art) /\
  cx.layouts = layouts /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot layouts target /\
  machine_well_typed am /\
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods am /\
  context_well_typed cx /\
  ALOOKUP cx.sources target = SOME mods /\
  cx.txn.target = target /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP am.immutables target = SOME imms ==>
  checked_deployment_constants_ready cx am target mods
Proof
  strip_tac >> gvs[] >>
  drule_all check_contract_evaluate_all_constants >>
  rw[IS_SOME_EXISTS] >>
  irule checked_deployment_constants_ready_from_success >>
  simp[get_tenv_def] >> metis_tac[]
QED

Theorem send_call_value_preserves_tv[local]:
  send_call_value mut cx st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), preserves_tv_def] >>
  TRY (qpat_x_assum `assert _ _ _ = _` mp_tac >> rw[assert_def] >> gvs[]) >>
  imp_res_tac transfer_value_scopes >>
  imp_res_tac transfer_value_immutables >>
  gvs[preserves_tv_def]
QED
Theorem call_lock_action_preserves_tv[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[] >>
  gvs[return_def, raise_def, preserves_tv_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def, preserves_tv_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[preserves_tv_def]
QED

Theorem call_unlock_action_preserves_immutables[local]:
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  gvs[]
QED

Theorem call_body_prefix_preserves_tv[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac call_lock_action_preserves_tv >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

Theorem call_body_prefix_lock_preserves_tv[local]:
  (do
     (case cx.nonreentrant_slot of
        NONE => raise (Error (TypeError "nonreentrant slot missing"))
      | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view);
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

(* Existing frame relations inspect only the old projections. *)
Theorem oracle_fields_frame_invariants[local,simp]:
  (preserves_tv cx (st with <|outcomes := orc; requests := rqs|>) st' <=>
   preserves_tv cx st st') /\
  (preserves_immutables_dom cx
     (st with <|outcomes := orc; requests := rqs|>) st' <=>
   preserves_immutables_dom cx st st')
Proof
  simp[preserves_tv_def, preserves_immutables_dom_def]
QED

Theorem preserves_tv_initial_immutables_lookup[local]:
  !orc rqs cx am_c env st src id tv x.
    preserves_tv cx (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) st ==>
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
    ?y.
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[preserves_tv_def, initial_state_def] >>
  metis_tac[]
QED

Theorem preserves_tv_unlock_abstract_machine_immutables_lookup[local]:
  preserves_tv cx (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) st_body /\
  st_unlocked.immutables = st_body.immutables /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[abstract_machine_from_state_def] >>
  drule (SRULE [] preserves_tv_initial_immutables_lookup) >>
  disch_then drule >>
  rw[] >>
  metis_tac[]
QED

Theorem call_external_function_deploy_normal_success_lookup_transport:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) = (INL (),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_deploy_return_success_lookup_transport:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) = (INR (ReturnException v_ret),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_success_result_cases[local]:
  (\(res,am_out,rqs). (res,am_out,rqs))
    (case body_res of
       (INL (), st) =>
         (case unlock st of
            (INL u, st') => (INL NoneV, abstract_machine_from_state srcs exps layouts st', st'.requests)
          | (INR e, st') => (INR e, am, st'.requests))
     | (INR (ReturnException v_ret), st) =>
         (case unlock st of
            (INL u, st') =>
              (case evaluate_type tenv ret of
                 NONE => (INR (Error (TypeError "eval ret")), am, st'.requests)
               | SOME tv =>
                   case safe_cast tv v_ret of
                     NONE => (INR (Error (TypeError "ext cast ret")), am, st'.requests)
                   | SOME v_cast =>
                       (INL v_cast, abstract_machine_from_state srcs exps layouts st', st'.requests))
          | (INR e, st') => (INR e, am, st'.requests))
     | (INR e, st) => (INR e, am, st.requests)) = (INL v, am_out, rqs) ==>
  ((?st_body st_unlocked u.
      body_res = (INL (), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked) \/
   (?v_ret st_body st_unlocked u tv v_cast.
      body_res = (INR (ReturnException v_ret), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      evaluate_type tenv ret = SOME tv /\
      safe_cast tv v_ret = SOME v_cast /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked))
Proof
  PairCases_on `body_res` >>
  Cases_on `body_res0` >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem call_external_function_deploy_success_cases:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  ?s1 dflt_vs s2 env res st_body st_unlocked.
    send_call_value mut cx
      (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>) =
      (INL (),s1) /\
    eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) s1 =
      (INL dflt_vs,s2) /\
    bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME env /\
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       eval_stmts cx body
     od) (s2 with scopes := [env]) = (res,st_body) /\
    (res = INL () \/ ?v_ret. res = INR (ReturnException v_ret)) /\
    (if nr /\ ~(mut = View \/ mut = Pure) then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st_body = (INL (),st_unlocked) /\
    am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
    rqs = st_unlocked.requests
Proof
  strip_tac >> drule call_external_function_success_phases >> simp[]
QED

Theorem call_locked_body_preserves_tv[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     eval_stmts cx body
   od) st = (res,rt) ==>
  preserves_tv cx st rt
Proof
  qmatch_goalsub_abbrev_tac `ignore_bind lock _ st` >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `lock st` >> Cases_on `q` >> simp[] >> strip_tac >>
  `preserves_tv cx st r` by
    (unabbrev_all_tac >> drule call_lock_action_preserves_tv >> simp[]) >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  gvs[] >> metis_tac[preserves_tv_trans]
QED

Theorem call_external_function_deploy_success_preserves_immutable_type_tags_from_constants[local]:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  strip_tac >>
  drule_all call_external_function_deploy_success_cases >> strip_tac >>
  drule send_call_value_preserves_tv >>
  drule eval_external_defaults_preserves_tv >>
  drule call_locked_body_preserves_tv >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `nr /\ ~(mut = View \/ mut = Pure)` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  simp[preserves_tv_def, initial_state_def, abstract_machine_from_state_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem send_call_value_preserves_immutables[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     type_check_def, assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_immutables >>
  gvs[]
QED

Theorem call_lock_action_preserves_immutables[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[]
QED


Theorem bind_arguments_length_c53[local]:
  !tenv args vs env.
    bind_arguments tenv args vs = SOME env ==> LENGTH args = LENGTH vs
Proof
  Induct_on `args` >> simp[bind_arguments_def] >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[bind_arguments_def] >>
  Cases_on `evaluate_type tenv h'1` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv args t` >> simp[] >>
  strip_tac >> res_tac
QED

Theorem call_external_function_exact_args_rewrites_c53[local]:
  bind_arguments (type_env_all_modules all_mods) args vals = SOME scope ==>
  LENGTH vals = LENGTH args /\
  DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts = [] /\
  vals ++ [] = vals
Proof
  strip_tac >>
  `LENGTH vals = LENGTH args` by metis_tac[bind_arguments_length_c53] >>
  simp[]
QED

Theorem transfer_value_no_type_error_c53[local]:
  !from to amount st s.
    FST (transfer_value from to amount st) <> INR (Error (TypeError s))
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem transfer_value_accounts_well_typed_c53[local]:
  !from to amount st.
    accounts_well_typed st.accounts ==>
    accounts_well_typed (SND (transfer_value from to amount st)).accounts
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >>
  simp[vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> decide_tac
QED

Theorem send_call_value_no_control_c53:
  send_call_value mut cx st = (INR exc,st') ==> no_control_exc exc
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
  >- (irule transfer_value_no_control >>
      qexistsl [`cx.txn.value`, `cx.txn.sender`, `st`, `st'`, `cx.txn.target`] >>
      simp[]) >>
  simp[no_control_exc_def]
QED

Theorem send_call_value_no_type_error_c53:
  no_type_error_eval (send_call_value mut cx st)
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def,
     vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `mut = Payable` >> gvs[return_def, raise_def] >>
  metis_tac[transfer_value_no_type_error_c53]
QED

Theorem send_call_value_preserves_scopes_c53[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem send_call_value_accounts_well_typed_c53:
  accounts_well_typed st.accounts /\
  send_call_value mut cx st = (res,st') ==>
  accounts_well_typed st'.accounts
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  `accounts_well_typed
     (SND (transfer_value cx.txn.sender cx.txn.target cx.txn.value st)).accounts` by
    metis_tac[transfer_value_accounts_well_typed_c53] >>
  gvs[]
QED

Theorem call_lock_action_preserves_accounts_c53:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_action_preserves_scopes_c53[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready_c53:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env] with <|outcomes := orc; requests := rqs|>) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes_c53 >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem call_lock_action_no_control_c53:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
   else return ()) st = (INR exc,st') ==>
  no_control_exc exc
Proof
  Cases_on `nr` >> gvs[return_def, raise_def, no_control_exc_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, no_control_exc_def] >>
  strip_tac >> drule acquire_nonreentrant_lock_no_control >>
  simp[no_control_exc_def]
QED

Theorem call_entry_eval_no_loop_control_c53:
  stmts_no_control_escape body /\
  (do
     send_call_value mut cx;
     dflt_vs <- eval_external_defaults cx es;
     case bind_arguments tenv args (vals ++ dflt_vs) of
       NONE => raise (Error (RuntimeError "call bind_arguments"))
     | SOME env => do
         set_scopes [env];
         (if nr then
            case cx.nonreentrant_slot of
              NONE => raise (Error (TypeError "nonreentrant slot missing"))
            | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
          else return ());
         eval_stmts cx body
       od
   od) st = (INR exc,rt) ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  rw[bind_def, ignore_bind_def, set_scopes_def] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac send_call_value_no_control_c53 >>
  imp_res_tac eval_external_defaults_no_control >>
  imp_res_tac stmts_no_control_escape_eval_stmts_no_loop_control >>
  gvs[no_control_exc_def] >>
  Cases_on `bind_arguments tenv args (vals ++ dflt_vs)` >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, no_control_exc_def] >>
  imp_res_tac acquire_nonreentrant_lock_no_control >>
  imp_res_tac stmts_no_control_escape_eval_stmts_no_loop_control >>
  gvs[no_control_exc_def]
QED

Theorem call_lock_action_no_type_error_c53:
  (nr ==> cx.nonreentrant_slot <> NONE) ==>
  no_type_error_eval
    ((if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem unlock_action_no_control_c53:
  (if nr /\ mut <> View /\ mut <> Pure then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (INR exc,st') ==>
  no_control_exc exc
Proof
  rw[] >> gvs[return_def, no_control_exc_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, no_control_exc_def] >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem call_external_function_no_loop_control_c53[local]:
  stmts_no_control_escape body /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am',rqs) ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `if cx.in_deploy then evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `pair_CASE entry` >>
  `!exc rt. entry = (INR exc,rt) ==>
     exc <> BreakException /\ exc <> ContinueException` by
    (qpat_x_assum `(\(res,am_out,rqs). _) _ = _` kall_tac >>
     unabbrev_all_tac >> rpt gen_tac >> disch_tac >>
     drule_at (Pos last) call_entry_eval_no_loop_control_c53 >> simp[]) >>
  Cases_on `entry` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `ignore_bind _ _ _ = _` kall_tac >>
  qpat_x_assum `(\(res,am_out,rqs). _) _ = _` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac unlock_action_no_control_c53 >> gvs[no_control_exc_def]
QED




Theorem unlock_action_no_type_error_c53:

  no_type_error_eval
    ((if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_action_frame_c53:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,rt) ==>
  rt.scopes = st.scopes /\ rt.immutables = st.immutables /\ rt.accounts = st.accounts
Proof
  strip_tac >> drule call_lock_action_preserves_scopes_c53 >>
  drule call_lock_action_preserves_immutables >>
  drule call_lock_action_preserves_accounts_c53 >> simp[]
QED

Theorem checked_external_locked_body_sound:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  body_entry_ready art cx scope st /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     eval_stmts cx body
   od) st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\ no_type_error_result res /\
  (!v. res = INR (ReturnException v) ==>
    ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v)
Proof
  strip_tac >> drule_all checked_external_declaration_static >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `ignore_bind lock _ st` >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `lock st` >> Cases_on `q` >> simp[] >> strip_tac >>
  `r.scopes = st.scopes /\ r.immutables = st.immutables /\ r.accounts = st.accounts` by
    (unabbrev_all_tac >> drule call_lock_action_frame_c53 >> simp[])
  >- (`body_entry_ready art cx scope r` by gvs[body_entry_ready_def, state_well_typed_def] >>
      `eval_stmts cx body r = (res,rt)` by fs[] >>
      drule_all checked_explicit_external_current_body_sound >> simp[])
  >> `no_type_error_eval (lock st)` by
       (unabbrev_all_tac >> irule call_lock_action_no_type_error_c53 >>
        gvs[IS_SOME_EXISTS] >> strip_tac >> first_x_assum drule >>
        strip_tac >> simp[]) >>
  `no_control_exc y` by
    (unabbrev_all_tac >> drule call_lock_action_no_control_c53 >> simp[]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      body_entry_ready_def, state_well_typed_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def, no_control_exc_def]
QED

Theorem send_call_value_state_sound_c53:
  state_well_typed st /\ accounts_well_typed st.accounts /\
  send_call_value mut cx st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\
  rt.immutables = st.immutables /\ no_type_error_result res
Proof
  strip_tac >> drule send_call_value_preserves_scopes_c53 >>
  drule send_call_value_preserves_immutables >>
  drule_all send_call_value_accounts_well_typed_c53 >>
  mp_tac (Q.INST [`st` |-> `st`, `mut` |-> `mut`, `cx` |-> `cx`]
    send_call_value_no_type_error_c53) >>
  gvs[state_well_typed_def, vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED

Theorem checked_external_defaults_body_sound:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  (do
     dvs <- eval_external_defaults cx (DROP k dflts);
     case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
       NONE => raise (Error (RuntimeError "call bind_arguments"))
     | SOME scope => do
         set_scopes [scope];
         (if nr then
            case cx.nonreentrant_slot of
              NONE => raise (Error (TypeError "nonreentrant slot missing"))
            | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
          else return ());
         eval_stmts cx body
       od
   od) st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\ no_type_error_result res /\
  (!v. res = INR (ReturnException v) ==>
    ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v)
Proof
  strip_tac >>
  drule_all checked_external_empty_frame_ready >> strip_tac >>
  drule_all checked_external_suffix_static >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qpat_x_assum `bind _ _ st = _` mp_tac >> pure_rewrite_tac[bind_def] >>
  Cases_on `eval_external_defaults cx (DROP k dflts) st` >> Cases_on `q` >> simp[] >>
  `state_well_typed r /\ accounts_well_typed r.accounts /\ no_type_error_result (FST (eval_external_defaults cx (DROP k dflts) st))` by
    (drule_all eval_external_defaults_type_sound >> simp[]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx r.immutables` by
    (drule_all eval_external_defaults_immutables_ready >> simp[])
  >- (rename1 `eval_external_defaults cx (DROP k dflts) st = (INL dvs,r)` >>
      Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
      simp[raise_def, bind_def, ignore_bind_def, set_scopes_def, return_def]
      >- (rpt strip_tac >> gvs[raise_def, vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      strip_tac >>
      `scope_well_typed x` by metis_tac[bind_arguments_scope_well_typed_from_success] >>
      `body_entry_ready art cx x (r with scopes := [x])` by
        gvs[body_entry_ready_def, state_well_typed_def] >>
      qpat_assum `cx = _` (fn th =>
        qpat_x_assum `pair_CASE _ _ = (res,rt)`
          (assume_tac o REWRITE_RULE [GSYM th])) >>
      drule_all (SRULE [bind_def, ignore_bind_def] checked_external_locked_body_sound) >> simp[])
  >> strip_tac >> gvs[] >> drule eval_external_defaults_no_control >>
  strip_tac >> gvs[no_control_exc_def,
    vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_external_entry_sound:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables /\
  (do
     send_call_value mut cx;
     dvs <- eval_external_defaults cx (DROP k dflts);
     case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
       NONE => raise (Error (RuntimeError "call bind_arguments"))
     | SOME scope => do
         set_scopes [scope];
         (if nr then
            case cx.nonreentrant_slot of
              NONE => raise (Error (TypeError "nonreentrant slot missing"))
            | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
          else return ());
         eval_stmts cx body
       od
   od) st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\ no_type_error_result res /\
  (!v. res = INR (ReturnException v) ==>
    ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v)
Proof
  strip_tac >> qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[bind_def, ignore_bind_def] >>
  Cases_on `send_call_value mut cx st` >> Cases_on `q` >> simp[] >> strip_tac >>
  drule_all send_call_value_state_sound_c53 >> strip_tac
  >- (`immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx r.immutables` by metis_tac[] >>
      qpat_assum `cx = _` (fn th =>
        qpat_x_assum `bind _ _ r = (res,rt)`
          (assume_tac o REWRITE_RULE [GSYM th])) >>
      drule_all (SRULE [ignore_bind_def] checked_external_defaults_body_sound) >> simp[])
  >> `no_control_exc y` by (drule external_entry_send_no_control >> simp[]) >>
  gvs[no_control_exc_def, vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem call_lock_send_eval_prefix_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       send_call_value mut cx;
       eval_stmts cx body
     od (initial_state am [scope] with <|outcomes := orc; requests := rqs|>))
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `ALL_DISTINCT (MAP FST args)` by
    (`check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
       (irule check_contract_runtime_function_body_MEM >> simp[] >>
        qexistsl [`tx.function_name`, `raw`, `External`] >> simp[]) >>
     gvs[check_function_body_def, params_ok_def]) >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[checked_contract_runtime_ready_def,
              immutables_ready_initial_evaluation_context_source] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
       bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
                 NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock
                   (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (`r''.scopes = [scope] /\ r''.immutables = am.immutables /\ state_well_typed r''` by
            (irule call_lock_send_prefix_body_state_ready_c53 >>
             simp[bind_def, ignore_bind_def] >>
             qexistsl [`initial_evaluation_context am.sources am.layouts tx src`, `mut`, `nr`, `orc`, `rqs`] >>
             simp[]) >>
          `accounts_well_typed r.accounts` by
            (imp_res_tac call_lock_action_preserves_accounts_c53 >>
             gvs[initial_state_accounts_well_typed_simple]) >>
          `accounts_well_typed r''.accounts` by
            (imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_eval_def] >>
          irule checked_explicit_external_post_prefix_body_no_type_error_selected >>
          simp[] >>
          conj_tac
          >- metis_tac[checked_explicit_external_body_call_evaluation_safe] >>
          qexistsl [`am`, `args`, `art`, `dflts`, `mods`, `mut`, `nr`, `raw`,
                    `ret`, `src`, `ts`, `tx`, `vals`] >>
          simp[]) >>
      `no_type_error_eval
         (send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r)` by
        simp[send_call_value_no_type_error_c53] >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]) >>
  `nr ==> (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot <> NONE` by (
    strip_tac >>
    `External <> Deploy` by simp[] >>
    `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
      metis_tac[check_contract_runtime_function_body_MEM] >>
    gvs[check_function_body_def, initial_evaluation_context_def,
        optionTheory.IS_SOME_EXISTS]) >>
  `no_type_error_eval
     ((if nr then
         case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock
             (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
             (mut = View \/ mut = Pure)
       else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>))` by (
    irule call_lock_action_no_type_error_c53 >>
    qpat_assum `nr ==> _` ACCEPT_TAC) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED

Theorem call_lock_send_eval_return_typed_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do
     (if nr then
        case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock tx.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
     eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INR (ReturnException v),st')) ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[checked_contract_runtime_ready_def,
              immutables_ready_initial_evaluation_context_source] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  qpat_x_assum `do _; _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
                 NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock tx.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut
         (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (strip_tac >>
          `r''.scopes = [scope] /\ r''.immutables = am.immutables /\
           state_well_typed r''` by (
            irule call_lock_send_prefix_body_state_ready_c53 >>
            simp[] >>
            qexistsl [`initial_evaluation_context am.sources am.layouts tx src`,
                      `mut`, `nr`, `orc`, `rqs`] >>
            gvs[bind_def, ignore_bind_def, initial_evaluation_context_def]) >>
          `r.accounts =
             (initial_state am [scope] with <|outcomes := orc; requests := rqs|>).accounts` by (
            qpat_x_assum `(if nr then _ else _) _ = (INL (),r)` mp_tac >>
            simp[initial_evaluation_context_def] >>
            Cases_on `nr` >> gvs[return_def, raise_def] >>
            Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
            gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
            qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
            rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
               get_transient_storage_def, update_transient_def, return_def,
               raise_def, assert_def, check_def] >>
            gvs[AllCaseEqs(), return_def, raise_def]) >>
          `accounts_well_typed r.accounts` by
            gvs[initial_state_accounts_well_typed_simple] >>
          `accounts_well_typed r''.accounts` by (
            imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          `call_evaluation_safe
             (initial_evaluation_context am.sources am.layouts tx src)
             (int_calls_stmts body)` by
            metis_tac[checked_explicit_external_body_call_evaluation_safe] >>
          irule checked_explicit_external_post_prefix_body_return_typed_selected >>
          simp[] >> metis_tac[])
      >- (strip_tac >> drule send_call_value_no_control_c53 >>
          simp[no_control_exc_def]))
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(if nr then _ else _) _ = (INR (ReturnException v),st')` mp_tac >>
      simp[initial_evaluation_context_def] >>
      Cases_on `nr` >> gvs[return_def, raise_def, no_control_exc_def] >>
      Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
      gvs[raise_def, no_control_exc_def] >> strip_tac >>
      drule acquire_nonreentrant_lock_no_control >> simp[no_control_exc_def])
QED

Theorem call_lock_send_eval_return_typed_case_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (case (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock tx.target slot (mut = View \/ mut = Pure)
         else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) of
     (INL x,s'') =>
       (case send_call_value mut
          (initial_evaluation_context am.sources am.layouts tx src) s'' of
          (INL x,s'') =>
            eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body s''
        | (INR e,s'') => (INR e,s''))
   | (INR e,s'') => (INR e,s'')) = (INR (ReturnException v),st') ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  strip_tac >>
  irule call_lock_send_eval_return_typed_c53 >>
  simp[bind_def, ignore_bind_def] >>
  qexistsl [`am`, `args`, `art`, `body`, `dflts`, `mut`, `nr`, `orc`, `raw`,
            `rqs`, `scope`, `src`, `st'`, `ts`, `tx`, `vals`] >>
  asm_rewrite_tac[]
QED

Theorem call_external_function_exact_selected_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret = (res,am',rqs) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by metis_tac[call_tx_well_typed_initial_context] >>
  `state_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) /\
   accounts_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def, scope_well_typed_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    metis_tac[checked_contract_runtime_ready_def,
              immutables_ready_initial_evaluation_context_source] >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_def, LET_THM] >>
  `cx.in_deploy = F` by simp[initial_evaluation_context_def] >>
  qpat_assum `cx.in_deploy = F` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  IF_CASES_TAC >- simp[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  `state_well_typed r /\ accounts_well_typed r.accounts /\ no_type_error_result q /\
   (!v. q = INR (ReturnException v) ==>
     ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v)` by
    (qpat_x_assum `entry _ = _` mp_tac >>
     simp_tac bool_ss [Abbr `entry`] >> strip_tac >>
     `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx
       (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>).immutables` by
       (simp_tac (srw_ss()) [initial_state_def] >> metis_tac[]) >>
     drule_all checked_external_entry_sound >> simp[]) >>
  qabbrev_tac `unlock = (if nr /\ mut <> View /\ mut <> Pure then
    case cx.nonreentrant_slot of NONE => return ()
    | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ())` >>
  `no_type_error_eval (unlock r)` by
    (simp_tac bool_ss [Abbr `unlock`] >> irule unlock_action_no_type_error_c53) >>
  Cases_on `q` >> simp_tac (srw_ss()) []
  >- (Cases_on `unlock r` >> Cases_on `q` >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `y` >> simp_tac (srw_ss()) [] >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
           vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  `?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v` by
    metis_tac[] >>
  drule vyperTypingTheory.safe_cast_well_typed >> strip_tac >>
  Cases_on `unlock r` >> Cases_on `q` >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >> rpt strip_tac >> gvs[]
QED

Theorem checked_explicit_external_entry_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  call_external_function orc am (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (res,am',rqs) ==>
  no_type_error_result res
Proof
  metis_tac[call_external_function_exact_selected_no_type_error_c53]
QED
Theorem initial_state_immutables[local]:
  (initial_state am scs).immutables = am.immutables
Proof
  simp[initial_state_def]
QED

Theorem preserves_immutables_dom_same_initial_from_mid[local]:
  st0.immutables = am_c.immutables /\
  (?st_mid. st_mid.immutables = am_c.immutables /\
            preserves_immutables_dom cx st_mid st') ==>
  preserves_immutables_dom cx st0 st'
Proof
  rw[preserves_immutables_dom_def] >> metis_tac[]
QED

Theorem preserves_immutables_dom_eq_local[local]:
  st'.immutables = st.immutables ==> preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans_local[local]:
  preserves_immutables_dom cx st1 st2 /\
  preserves_immutables_dom cx st2 st3 ==>
  preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  `?imms2. ALOOKUP st2.immutables cx.txn.target = SOME imms2` by
    (gvs[IS_SOME_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem call_body_prefix_preserves_immutables_dom[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) = (res,st')) ==>
  preserves_immutables_dom cx
    (initial_state am_c [env] with <|outcomes := orc; requests := rqs|>) st'
Proof
  rw[bind_def, ignore_bind_def] >>
  imp_res_tac call_lock_action_preserves_immutables >>
  gvs[AllCaseEqs()] >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INL (),s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INR e,s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (qpat_x_assum `return () _ = (INL (),s'')` mp_tac >>
       rw[return_def, initial_state_def]) >>
  imp_res_tac send_call_value_preserves_immutables >>
  imp_res_tac eval_stmts_preserves_immutables_addr_dom >>
  imp_res_tac eval_stmts_preserves_immutables_dom >>
  fs[preserves_immutables_dom_def, initial_state_immutables] >> rw[] >> gvs[]
QED

Theorem preserves_immutables_dom_final_lookup_exists_in_initial[local]:
  preserves_immutables_dom cx st0 st_body /\
  st0.immutables = am_c.immutables /\
  st_unlocked.immutables = st_body.immutables /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP st_unlocked.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[preserves_immutables_dom_def] >>
  Cases_on `ALOOKUP am_c.immutables cx.txn.target` >>
  gvs[get_source_immutables_def]
  >- (Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
      gvs[get_source_immutables_def] >>
      qpat_x_assum `!tgt. _` (qspec_then `cx.txn.target` mp_tac) >>
      simp[IS_SOME_EXISTS]) >>
  rename1 `ALOOKUP am_c.immutables cx.txn.target = SOME imms0` >>
  Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP st_body.immutables cx.txn.target = SOME imms1` >>
  qpat_x_assum `!src' n. _`
    (qspecl_then [`src`,`id`] mp_tac) >>
  simp[IS_SOME_EXISTS, EXISTS_PROD]
QED

(* The current concrete deployment API still starts with NONE/[] (TASK027). *)
Theorem call_body_prefix_preserves_immutables_dom_simple[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (res,st')) ==>
  preserves_immutables_dom cx (initial_state am_c [env]) st'
Proof
  mp_tac (Q.INST [`orc` |-> `NONE`, `rqs` |-> `[]`]
    call_body_prefix_preserves_immutables_dom) >> simp[initial_state_def]
QED

(* Compose the public domain facts rather than importing the evaluator's
   local mutual-induction theorem. *)
Theorem entry_eval_preserves_immutables_dom[local]:
  (eval_exprs cx es st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (eval_stmts cx body st = (res',st') ==> preserves_immutables_dom cx st st')
Proof
  conj_tac >> strip_tac >> rw[preserves_immutables_dom_def] >>
  FIRST [
    drule_all eval_exprs_preserves_immutables_addr_dom >> simp[] >> NO_TAC,
    drule_all eval_exprs_preserves_immutables_dom >> simp[] >> NO_TAC,
    drule_all eval_stmts_preserves_immutables_addr_dom >> simp[] >> NO_TAC,
    drule_all eval_stmts_preserves_immutables_dom >> simp[]]
QED

Theorem actual_entry_prefix_preserves_immutables_dom[local]:
  send_call_value mut cx st0 = (INL (),s1) /\
  eval_external_defaults cx es s1 = (INL dvs,s2) /\
  ignore_bind
    (if nr then case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
     else return ()) (eval_stmts cx body) (s2 with scopes := [env]) = (res,rt) ==>
  preserves_immutables_dom cx st0 rt
Proof
  strip_tac >>
  drule send_call_value_preserves_immutables >> strip_tac >>
  qpat_x_assum `eval_external_defaults _ _ _ = _` mp_tac >>
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (s1 with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  drule (cj 1 entry_eval_preserves_immutables_dom) >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp_tac bool_ss [ignore_bind_def, bind_def] >>
  Cases_on `(if nr then case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
     else return ()) (r with scopes := [env])` >>
  drule call_lock_action_preserves_immutables >> strip_tac >>
  Cases_on `q` >> simp[] >> strip_tac >> gvs[]
  >- (drule (cj 2 entry_eval_preserves_immutables_dom) >> strip_tac >>
      irule preserves_immutables_dom_trans_local >>
      qexists `r''` >>
      gvs[preserves_immutables_dom_def]) >>
  gvs[preserves_immutables_dom_def]
QED

Theorem call_external_function_deploy_success_final_lookup_source_exists_in_constants[local]:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[]
  >- (drule_all actual_entry_prefix_preserves_immutables_dom >> strip_tac >>
      `st_unlocked.immutables = st_body.immutables` by
        (Cases_on `nr` >> gvs[return_def] >>
         Cases_on `mut = View` >> gvs[return_def] >>
         Cases_on `mut = Pure` >> gvs[return_def] >>
         Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
         imp_res_tac release_nonreentrant_lock_immutables) >>
      gvs[abstract_machine_from_state_def] >>
      irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]) >>
  drule_all actual_entry_prefix_preserves_immutables_dom >> strip_tac >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `nr` >> gvs[return_def] >>
     Cases_on `mut = View` >> gvs[return_def] >>
     Cases_on `mut = Pure` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  gvs[abstract_machine_from_state_def] >>
  irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]
QED

Theorem deploy_call_success_transports_bare_global_readiness_clause[local]:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_assum (irule_at Any) >>
  first_assum (irule_at Any)
QED

Theorem deploy_context_constants_bare_globals_type_ready[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  `(((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps)) with
      immutables updated_by CONS (deploy_tx.target,imms)) =
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
              exports updated_by CONS (deploy_tx.target,exps)|>)` by simp[] >>
  gvs[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  strip_tac >>
  first_x_assum (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`, `imms`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps))`] mp_tac) >>
  gvs[get_tenv_def, initial_evaluation_context_def, alistTheory.ALOOKUP_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv`,`v`] mp_tac) >>
  simp[]
QED

Theorem deploy_call_success_scalar_bare_global_type_from_constants[local]:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret = (INL v_out,am_out,rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  gvs[] >>
  rename1 `FLOOKUP _ _ = SOME (tv0,y0)` >>
  `evaluate_type (type_env_all_modules all_mods) ty = SOME tv0` by
    (first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv0`,`y0`] mp_tac) >>
     simp[]) >>
  `?y'.
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y')` by
    (drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
     simp[]) >>
  gvs[]
QED

Theorem deploy_constructor_success_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function orc
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor,rqs) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function orc
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor,rqs)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  irule deploy_call_success_scalar_bare_global_type_from_constants >>
  simp[] >>
  qexistsl
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `am_c`, `am_ctor`, `args`, `body`, `call_art`, `cx0`, `dflts`,
     `id`, `mut`, `nr`, `orc`, `ret`, `rqs`, `src`, `ts`, `v`, `v'`, `deploy_tx.args`] >>
  gvs[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`src'`,`id'`,`ty'`,`tv'`,`v''`] mp_tac) >>
  simp[]
QED

Theorem evaluate_all_constants_preserves_layouts[local]:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.layouts = am.layouts
Proof
  simp[evaluate_all_constants_def] >>
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qspec_tac (`constants_order mods`, `mods`) >>
  Induct >- rw[evaluate_module_constants_def] >>
  Cases_on `h` >>
  rw[evaluate_module_constants_def] >>
  gvs[AllCaseEqs(), merge_constants_def] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_deploy_success_preserves_layouts:
  !orc rqs am cx nr mut ts all_mods args dflts vals body ret v am_out am_c.
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  am_out.layouts = am.layouts
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  drule evaluate_all_constants_preserves_layouts >>
  strip_tac >>
  strip_tac >>
  gvs[abstract_machine_from_state_def]
QED

Theorem load_contract_success_constructor_constants_context:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) ==>
  ?imms ts mut nr args dflts ret body v am_ctor am_c.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE deploy_tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function orc
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      nr mut ts mods args dflts deploy_tx.args body ret = (INL v, am_ctor, rqs) /\
    evaluate_all_constants
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      deploy_tx.target mods = SOME am_c /\
    am_ctor.layouts = am.layouts /\
    am_deployed = finalize_pending_deletions
      (am_ctor with sources updated_by CONS (deploy_tx.target,mods))
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  qspecl_then
    [`orc`, `rqs`, `am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `((initial_evaluation_context ((deploy_tx.target,mods)::am.sources)
          am.layouts deploy_tx NONE) with in_deploy := T)`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`]
    mp_tac call_external_function_deploy_success_evaluate_all_constants >>
  simp[] >> strip_tac >>
  qexists `am_c` >>
  gvs[initial_evaluation_context_def] >>
  qspecl_then
    [`orc`, `rqs`, `am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `<|stk := [(NONE,deploy_tx.function_name)]; txn := deploy_tx;
        sources := (deploy_tx.target,mods)::am.sources; layouts := am.layouts;
        in_deploy := T;
        nonreentrant_slot := lookup_nonreentrant_slot am.layouts deploy_tx.target|>`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`]
    mp_tac call_external_function_deploy_success_preserves_layouts >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_constructor_context_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function orc
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
    deploy_tx.args body ret = (INL v',am_ctor,rqs) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function orc
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
     deploy_tx.args body ret = (INL v',am_ctor,rqs)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  metis_tac[deploy_call_success_scalar_bare_global_type_from_constants]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_clause[local]:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type
      (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
      ty = SOME tv
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  gvs[get_tenv_def, initial_evaluation_context_def] >>
  irule load_contract_constructor_context_bare_global_type_from_constants >>
  gvs[initial_evaluation_context_def] >>
  qexistsl
    [`am`, `am_c`, `am_ctor`, `args`, `body`, `call_art`, `deploy_tx`,
     `dflts`, `exps`, `id`, `mut`, `nr`, `orc`, `ret`, `rqs`, `src`, `v`, `v'`] >>
  gvs[]
QED

Theorem deployed_toplevel_vtypes_immutables_ready_clause[local]:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type
       (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
       ty = SOME tv) ==>
  !src id ty ts.
    FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
    get_module_code
      (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE) src = SOME ts ==>
    (!is_transient typ id_str.
       find_var_decl_by_name id ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
       typ = ty) /\
    (!is_transient kt vt id_str.
       find_var_decl_by_name id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
       F) /\
    (find_var_decl_by_name id ts = NONE ==>
     !tv v.
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => []))
         id = SOME (tv,v) ==>
       evaluate_type
         (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
         ty = SOME tv)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  `ALOOKUP ((deploy_tx.target,mods)::am_ctor.sources) call_tx.target = SOME mods` by
    simp[] >>
  `(!src id vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype (type_env_all_modules mods) vt) /\
    (!src id ty.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==>
      ?ts is_transient typ id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_name id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
        typ = ty /\
        IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str)) /\
    (!src id kt vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
      ?ts is_transient id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_name id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str))` by
    (irule check_contract_toplevel_vtypes_consistent_initial >> simp[]) >>
  rpt conj_tac
  >- (Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >> rpt strip_tac >>
     Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
     >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
           (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
     `bare_ty = ty` by
       (drule check_contract_bare_globals_consistent_initial >>
        disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
        simp[get_module_code_def, initial_evaluation_context_def] >>
        rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     gvs[] >>
     qpat_x_assum `!src' id' ty' tv' v'. FLOOKUP call_art.cta_bare_globals (src',id') = SOME ty' /\ FLOOKUP _ id' = SOME (tv',v') ==> _`
       (qspecl_then [`src`,`id`,`bare_ty`,`tv`,`v`] mp_tac) >>
     simp[]
QED

Theorem deploy_context_constants_bare_globals_lookup_exists[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
  ?tv v.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v)
Proof
  rw[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  disch_then (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `am with exports updated_by CONS (deploy_tx.target,exps)`] mp_tac) >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  impl_tac >- gvs[initial_evaluation_context_def] >>
  rw[]
QED

Theorem call_external_function_deploy_success_final_lookup_exists_from_constants[local]:
  !orc rqs cx am nr mut ts all_mods args dflts vals body ret v am_out am_c src id.
    cx.in_deploy /\
    call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
      (INL v, am_out, rqs) /\
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id) ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id)
Proof
  rw[IS_SOME_EXISTS, EXISTS_PROD] >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  simp[IS_SOME_EXISTS]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_exists_clause[local]:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id)
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  qspecl_then [`orc`, `rqs`, `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am with <|exports updated_by CONS (deploy_tx.target,exps);
              immutables updated_by CONS (deploy_tx.target,imms)|>`,
    `nr`, `mut`, `case ALOOKUP mods NONE of NONE => [] | SOME ts => ts`, `mods`,
    `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`, `src`, `id`]
    mp_tac call_external_function_deploy_success_final_lookup_exists_from_constants >>
  simp[initial_evaluation_context_def] >>
  disch_then irule >>
  conj_tac
  >- (simp[IS_SOME_EXISTS, EXISTS_PROD] >>
      irule deploy_context_constants_bare_globals_lookup_exists >>
      qexistsl [`am`,`call_art`,`exps`,`imms`,`mods`,`ty`] >>
      gvs[]) >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_immutables_ready:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  immutables_ready call_art.cta_bare_globals call_art.cta_toplevel_vtypes
    (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE)
    am_deployed.immutables
Proof
  rw[immutables_ready_def]
  >- (simp[initial_evaluation_context_def] >>
      irule load_contract_deployed_bare_globals_immutables_ready_exists_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `mods`, `orc`, `rqs`, `ty`] >>
      gvs[])
  >- (irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `orc`, `rqs`, `src`, `v`] >>
      gvs[initial_evaluation_context_def])
  >- (irule (cj 1 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `mods`, `orc`, `rqs`, `src`, `ts`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id_str) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id_str = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id_str`, `mods`, `orc`, `rqs`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >- (strip_tac >>
      irule (cj 2 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `kt`, `mods`, `orc`, `rqs`, `src`, `ts`, `ty`, `vt`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id_str) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id_str = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id_str`, `mods`, `orc`, `rqs`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >> irule (cj 3 deployed_toplevel_vtypes_immutables_ready_clause) >>
     qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `orc`, `rqs`, `src`, `ts`, `v`] >>
     gvs[initial_evaluation_context_def] >>
     rpt strip_tac >>
     drule load_contract_deployed_bare_globals_immutables_ready_clause >>
     strip_tac >>
     pop_assum (qspec_then `call_tx` mp_tac) >>
     simp[initial_evaluation_context_def] >>
     strip_tac >>
     qmatch_assum_rename_tac
       `FLOOKUP call_art.cta_bare_globals (_,bg_id) = SOME _` >>
     pop_assum (qspec_then `src'` assume_tac) >>
     pop_assum (qspec_then `bg_id` assume_tac) >>
     pop_assum (qspec_then `ty'` assume_tac) >>
     pop_assum (qspec_then `tv'` assume_tac) >>
     pop_assum (qspec_then `v'` mp_tac) >>
     simp[]
QED

Theorem evaluate_all_constants_preserves_exports[local]:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.exports = am.exports
Proof
  simp[evaluate_all_constants_def] >>
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qspec_tac (`constants_order mods`, `mods`) >>
  Induct >- rw[evaluate_module_constants_def] >>
  Cases_on `h` >>
  rw[evaluate_module_constants_def] >>
  gvs[AllCaseEqs(), merge_constants_def] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_deploy_success_preserves_exports[local]:
  cx.in_deploy /\
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out, rqs) ==>
  am_out.exports = am.exports
Proof
  strip_tac >>
  drule_all call_external_function_deploy_success_evaluate_all_constants >>
  strip_tac >>
  drule_all call_external_function_deploy_success_cases >>
  drule evaluate_all_constants_preserves_exports >>
  strip_tac >> strip_tac >>
  gvs[abstract_machine_from_state_def]
QED

Theorem load_contract_deployed_exports:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) ==>
  ALOOKUP am_deployed.exports deploy_tx.target = SOME exps
Proof
  strip_tac >>
  drule load_contract_success_cases >> strip_tac >>
  drule_at (Pos (el 2)) call_external_function_deploy_success_preserves_exports >>
  simp[]
QED

Theorem load_contract_establishes_checked_contract_runtime_ready:
  load_contract orc am deploy_tx mods exps = INL (am_deployed,rqs) /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME art /\
  exports_ok am_deployed.layouts call_tx.target mods exps /\
  call_tx.target = deploy_tx.target ==>
  checked_contract_runtime_ready art mods am_deployed call_tx
Proof
  rw[checked_contract_runtime_ready_def]
  >- (drule load_contract_success_cases >> strip_tac >> gvs[])
  >- (drule load_contract_deployed_exports >> gvs[])
  >> irule load_contract_establishes_immutables_ready
  >> qexistsl [`am`, `deploy_tx`, `exps`, `mods`, `orc`, `rqs`]
  >> simp[]
QED

(* The obsolete generated-getter materialisability pipeline formerly here
   tracked the pre-typed build_getter AST.  Selected getter soundness below
   now proceeds from checked_public_getter_body_typing_package and generic
   expression/statement preservation. *)

Definition getter_context_equiv_def[local]:
  getter_context_equiv cx1 cx2 <=>
    cx1.sources = cx2.sources /\
    cx1.layouts = cx2.layouts /\
    cx1.txn.target = cx2.txn.target
End

Theorem getter_context_equiv_initial_empty_tx[local]:
  getter_context_equiv
    (initial_evaluation_context sources layouts tx src)
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src)
Proof
  simp[getter_context_equiv_def, initial_evaluation_context_def]
QED

Theorem getter_context_equiv_get_tenv[local]:
  getter_context_equiv cx1 cx2 ==> get_tenv cx1 = get_tenv cx2
Proof
  rw[getter_context_equiv_def, get_tenv_def]
QED
Theorem getter_context_equiv_get_storage_backend[local]:
  getter_context_equiv cx1 cx2 ==>
  get_storage_backend cx1 is_transient = get_storage_backend cx2 is_transient
Proof
  Cases_on `is_transient` >>
  simp[getter_context_equiv_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def,
       FUN_EQ_THM]
QED

Theorem getter_context_equiv_read_storage_slot[local]:
  getter_context_equiv cx1 cx2 ==>
  read_storage_slot cx1 is_transient slot tv =
  read_storage_slot cx2 is_transient slot tv
Proof
  strip_tac >>
  drule getter_context_equiv_get_storage_backend >>
  disch_then (fn th => rewrite_tac[read_storage_slot_def, th])
QED

Theorem getter_context_equiv_get_immutables[local]:
  getter_context_equiv cx1 cx2 ==>
  get_immutables cx1 src = get_immutables cx2 src
Proof
  rw[getter_context_equiv_def, get_immutables_def,
     get_address_immutables_def, FUN_EQ_THM, bind_def]
QED

Theorem getter_context_equiv_read_place[local]:
  getter_context_equiv cx1 cx2 ==>
  read_place cx1 p = read_place cx2 p
Proof
  strip_tac >> Cases_on `p` >>
  simp[read_place_def, getter_context_equiv_read_storage_slot] >>
  drule getter_context_equiv_get_immutables >>
  disch_then (fn th => rewrite_tac[th])
QED

Theorem getter_context_equiv_place_type_value[local]:
  getter_context_equiv cx1 cx2 ==>
  place_type_value cx1 p = place_type_value cx2 p
Proof
  strip_tac >> Cases_on `p` >>
  simp[place_type_value_def] >>
  drule getter_context_equiv_get_immutables >>
  disch_then (fn th => rewrite_tac[th])
QED

Theorem getter_context_equiv_read_result[local]:
  getter_context_equiv cx1 cx2 ==>
  read_result cx1 tv = read_result cx2 tv
Proof
  strip_tac >> Cases_on `tv` >>
  simp[read_result_def, getter_context_equiv_read_place]
QED

Theorem getter_context_equiv_resolve_array_element[local]:
  !path slot tv. getter_context_equiv cx1 cx2 ==>
  resolve_array_element cx1 tr slot tv path =
  resolve_array_element cx2 tr slot tv path
Proof
  Induct_on `path` >- (Cases_on `tv` >> simp[resolve_array_element_def]) >>
  rpt gen_tac >> strip_tac >>
  `get_storage_backend cx1 tr = get_storage_backend cx2 tr` by
    metis_tac[getter_context_equiv_get_storage_backend] >>
  Cases_on `tv` >> simp[resolve_array_element_def] >>
  Cases_on `h` >> simp[resolve_array_element_def] >>
  Cases_on `v` >> simp[resolve_array_element_def] >>
  rename1 `ArrayTV etv bd` >> Cases_on `bd` >>
  simp[resolve_array_element_def]
QED

Theorem getter_context_equiv_extend_storage_place[local]:
  getter_context_equiv cx1 cx2 ==>
  extend_storage_place cx1 tr slot tv sb =
  extend_storage_place cx2 tr slot tv sb
Proof
  strip_tac >>
  `!slot tv path. resolve_array_element cx1 tr slot tv path =
                  resolve_array_element cx2 tr slot tv path` by
    metis_tac[getter_context_equiv_resolve_array_element] >>
  simp[oneline extend_storage_place_def]
QED

Theorem getter_context_equiv_extend_place[local]:
  getter_context_equiv cx1 cx2 ==>
  extend_place cx1 res sb = extend_place cx2 res sb
Proof
  strip_tac >>
  `!p. place_type_value cx1 p = place_type_value cx2 p` by
    metis_tac[getter_context_equiv_place_type_value] >>
  `!p. read_place cx1 p = read_place cx2 p` by
    metis_tac[getter_context_equiv_read_place] >>
  `!tr slot tv sb. extend_storage_place cx1 tr slot tv sb =
                  extend_storage_place cx2 tr slot tv sb` by
    metis_tac[getter_context_equiv_extend_storage_place] >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  simp[oneline extend_place_def]
QED

Theorem getter_context_equiv_select_result[local]:
  getter_context_equiv cx1 cx2 ==>
  select_result cx1 ty res sb = select_result cx2 ty res sb
Proof
  strip_tac >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  Cases_on `res` >>
  simp[select_result_def, getter_context_equiv_extend_place]
QED

Theorem getter_context_equiv_eval_Subscript[local]:
  getter_context_equiv cx1 cx2 /\
  eval_expr cx1 e1 = eval_expr cx2 e1 /\
  eval_expr cx1 e2 = eval_expr cx2 e2 ==>
  eval_expr cx1 (Subscript ty e1 e2) =
  eval_expr cx2 (Subscript ty e1 e2)
Proof
  rpt strip_tac >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  `!res. read_result cx1 res = read_result cx2 res` by
    metis_tac[getter_context_equiv_read_result] >>
  `!ty res sb. select_result cx1 ty res sb = select_result cx2 ty res sb` by
    metis_tac[getter_context_equiv_select_result] >>
  simp[Ntimes evaluate_def 2]
QED

Theorem eval_Name_context_irrelevant[local]:
  eval_expr cx1 (Name kt s) = eval_expr cx2 (Name kt s)
Proof
  simp[Ntimes evaluate_def 2]
QED

Theorem build_getter_eval_context_equiv[local]:
  !e kt vt n args ret exp cx1 cx2.
    build_getter e kt vt n = (args,ret,exp) /\
    getter_context_equiv cx1 cx2 /\
    eval_expr cx1 e = eval_expr cx2 e ==>
    eval_expr cx1 exp = eval_expr cx2 exp
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[]
  >- (first_x_assum irule >>
      conj_tac >-
        (irule getter_context_equiv_eval_Subscript >>
         simp[Ntimes evaluate_def 2]) >>
      simp[])
  >- (`eval_expr cx1 (Name kt (toString n)) =
       eval_expr cx2 (Name kt (toString n))` by
        simp[eval_Name_context_irrelevant] >>
      metis_tac[getter_context_equiv_eval_Subscript])
  >> first_x_assum irule >>
  conj_tac >-
    (`eval_expr cx1 (Name kt (toString n)) =
      eval_expr cx2 (Name kt (toString n))` by
       simp[eval_Name_context_irrelevant] >>
     metis_tac[getter_context_equiv_eval_Subscript]) >>
  simp[] >>
  `eval_expr cx1 (Name kt (toString n)) =
   eval_expr cx2 (Name kt (toString n))` by
    simp[eval_Name_context_irrelevant] >>
  metis_tac[getter_context_equiv_eval_Subscript]
QED

Theorem getter_context_equiv_lookup_global[local]:
  getter_context_equiv cx1 cx2 ==>
  lookup_global cx1 src n = lookup_global cx2 src n
Proof
  strip_tac >>
  `get_module_code cx1 src = get_module_code cx2 src` by
    gvs[getter_context_equiv_def, get_module_code_def] >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  `!tr src' id. lookup_var_slot_from_layout cx1 tr src' id =
                lookup_var_slot_from_layout cx2 tr src' id` by
    gvs[getter_context_equiv_def, lookup_var_slot_from_layout_def] >>
  `get_address_immutables cx1 = get_address_immutables cx2` by
    gvs[getter_context_equiv_def, get_address_immutables_def,
        FUN_EQ_THM] >>
  `!src'. get_immutables cx1 src' = get_immutables cx2 src'` by
    simp[get_immutables_def] >>
  `!tr slot tv. read_storage_slot cx1 tr slot tv =
                read_storage_slot cx2 tr slot tv` by
    metis_tac[getter_context_equiv_read_storage_slot] >>
  simp[lookup_global_def, bind_def, AllCaseEqs()]
QED

Theorem getter_context_equiv_eval_TopLevelName[local]:
  getter_context_equiv cx1 cx2 ==>
  eval_expr cx1 (TopLevelName ty key) =
  eval_expr cx2 (TopLevelName ty key)
Proof
  strip_tac >> PairCases_on `key` >>
  simp[Ntimes evaluate_def 2, getter_context_equiv_lookup_global]
QED

Theorem getter_context_equiv_eval_single_Return[local]:
  getter_context_equiv cx1 cx2 /\
  eval_expr cx1 exp = eval_expr cx2 exp ==>
  eval_stmts cx1 [Return (SOME exp)] =
  eval_stmts cx2 [Return (SOME exp)]
Proof
  rpt strip_tac >>
  `!tv. read_result cx1 tv = read_result cx2 tv` by
    metis_tac[getter_context_equiv_read_result] >>
  `eval_stmt cx1 (Return (SOME exp)) =
   eval_stmt cx2 (Return (SOME exp))` by
    simp[Ntimes evaluate_def 2, bind_def, AllCaseEqs()] >>
  once_rewrite_tac[evaluate_def] >>
  sym_tac >> once_rewrite_tac[evaluate_def] >> sym_tac >>
  simp[Ntimes evaluate_def 2, bind_def]
QED
Theorem build_getter_int_calls_empty[local]:
  !e kt vt n args ret exp.
    int_calls_expr e = [] /\
    build_getter e kt vt n = (args,ret,exp) ==>
    int_calls_expr exp = []
Proof
  recInduct build_getter_ind >> rpt strip_tac
  >- (Cases_on `is_ArrayT vt`
      >- (qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
          simp[Once build_getter_def] >>
          Cases_on `build_getter (Subscript vt e (Name kt (toString n)))
                      (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n)` >>
          Cases_on `r` >> gvs[] >>
          rpt strip_tac >> gvs[] >>
          qpat_x_assum `int_calls_expr _ = [] ==> int_calls_expr _ = []` irule >>
          simp[int_calls_expr_def]) >>
      qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
      simp[Once build_getter_def, int_calls_expr_def] >>
      rpt strip_tac >> gvs[int_calls_expr_def]) >>
  qpat_x_assum `build_getter e kt (HashMapT typ vtyp) n = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `build_getter
    (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
      (Name kt (toString n))) typ vtyp (SUC n)` >>
  Cases_on `r` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `int_calls_expr _ = [] ==> int_calls_expr _ = []` irule >>
  simp[int_calls_expr_def]
QED

Theorem selected_public_getter_body_int_calls_empty:
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  int_calls_stmts body = []
Proof
  rpt strip_tac >>
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (drule_all array_public_getter_tuple_shape >> strip_tac >> gvs[] >>
          `int_calls_expr (TopLevelName t (src,s)) = []` by
            simp[int_calls_expr_def] >>
          `int_calls_expr exp = []` by
            metis_tac[build_getter_int_calls_empty] >>
          simp[int_calls_stmt_def, int_calls_expr_def]) >>
      gvs[external_getter_tuple_def, getter_def] >>
      simp[int_calls_expr_def, int_calls_stmt_def]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  `int_calls_expr (TopLevelName NoneT (src,fn)) = []` by
    simp[int_calls_expr_def] >>
  `int_calls_expr exp = []` by
    metis_tac[build_getter_int_calls_empty] >>
  simp[int_calls_expr_def, int_calls_stmt_def]
QED

Theorem selected_public_getter_body_eval_context_equiv:
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  getter_context_equiv cx1 cx2 ==>
  ?exp. body = [Return (SOME exp)] /\
        eval_expr cx1 exp = eval_expr cx2 exp
Proof
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (rpt strip_tac >>
          drule_all array_public_getter_tuple_shape >> strip_tac >> gvs[] >>
          irule build_getter_eval_context_equiv >> simp[] >>
          metis_tac[getter_context_equiv_eval_TopLevelName]) >>
      rpt strip_tac >>
      gvs[external_getter_tuple_def] >>
      metis_tac[getter_context_equiv_eval_TopLevelName]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  rpt strip_tac >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule build_getter_eval_context_equiv >> simp[] >>
  metis_tac[getter_context_equiv_eval_TopLevelName]
QED


Theorem fn_sigs_consistent_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  cx1.in_deploy = cx2.in_deploy ==>
  (fn_sigs_consistent sigs cx1 <=> fn_sigs_consistent sigs cx2)
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem fn_sigs_declared_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  (!k. context_function_live cx1 k = context_function_live cx2 k) /\
  cx1.in_deploy = cx2.in_deploy ==>
  (fn_sigs_declared_complete sigs cx1 <=>
   fn_sigs_declared_complete sigs cx2)
Proof
  simp[fn_sigs_declared_complete_def]
QED

Theorem toplevel_vtypes_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  (!tr src id. lookup_var_slot_from_layout cx1 tr src id =
               lookup_var_slot_from_layout cx2 tr src id) ==>
  (toplevel_vtypes_complete vtypes cx1 <=>
   toplevel_vtypes_complete vtypes cx2)
Proof
  simp[toplevel_vtypes_complete_def]
QED

Theorem bare_globals_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (bare_globals_complete globals cx1 <=>
   bare_globals_complete globals cx2)
Proof
  simp[bare_globals_complete_def]
QED

Theorem bare_global_assignable_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (bare_global_assignable_complete globals cx1 <=>
   bare_global_assignable_complete globals cx2)
Proof
  simp[bare_global_assignable_complete_def]
QED

Theorem flag_members_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (flag_members_complete members cx1 <=>
   flag_members_complete members cx2)
Proof
  simp[flag_members_complete_def]
QED

Theorem env_context_consistent_context_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  current_module cx1 = current_module cx2 /\
  cx1.in_deploy = cx2.in_deploy /\
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  (!k. context_function_live cx1 k = context_function_live cx2 k) /\
  (!tr src id. lookup_var_slot_from_layout cx1 tr src id =
               lookup_var_slot_from_layout cx2 tr src id) ==>
  (env_context_consistent env cx1 <=> env_context_consistent env cx2)
Proof
  rpt strip_tac >>
  `fn_sigs_consistent env.fn_sigs cx1 <=>
   fn_sigs_consistent env.fn_sigs cx2` by
    (irule fn_sigs_consistent_context_cong >> simp[]) >>
  `fn_sigs_declared_complete env.fn_sigs cx1 <=>
   fn_sigs_declared_complete env.fn_sigs cx2` by
    (irule fn_sigs_declared_complete_context_cong >> simp[]) >>
  `toplevel_vtypes_complete env.toplevel_vtypes cx1 <=>
   toplevel_vtypes_complete env.toplevel_vtypes cx2` by
    (irule toplevel_vtypes_complete_context_cong >> simp[]) >>
  `bare_globals_complete env.bare_globals cx1 <=>
   bare_globals_complete env.bare_globals cx2` by
    (irule bare_globals_complete_context_cong >> simp[]) >>
  `bare_global_assignable_complete env.bare_global_assignable cx1 <=>
   bare_global_assignable_complete env.bare_global_assignable cx2` by
    (irule bare_global_assignable_complete_context_cong >> simp[]) >>
  `flag_members_complete env.flag_members cx1 <=>
   flag_members_complete env.flag_members cx2` by
    (irule flag_members_complete_context_cong >> simp[]) >>
  simp[env_context_consistent_def, fn_sigs_live_def]
QED

Theorem initial_env_context_consistent_empty_tx[local]:
  env_context_consistent env
    (initial_evaluation_context sources layouts tx src) ==>
  env_context_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src)
Proof
  strip_tac >>
  `env_context_consistent env
      (initial_evaluation_context sources layouts tx src) <=>
   env_context_consistent env
      (initial_evaluation_context sources layouts
        (empty_call_txn with target := tx.target) src)` by
    (irule env_context_consistent_context_cong >>
     simp[get_tenv_def, current_module_def, get_module_code_def,
          lookup_var_slot_from_layout_def, initial_evaluation_context_def,
          context_function_live_def, empty_call_txn_def]) >>
  metis_tac[]
QED

Theorem env_scopes_consistent_get_tenv_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  env_scopes_consistent env cx1 st ==>
  env_scopes_consistent env cx2 st
Proof
  simp[env_scopes_consistent_def] >>
  metis_tac[]
QED

Theorem initial_env_scopes_consistent_empty_tx[local]:
  env_scopes_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_scopes_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  `get_tenv (initial_evaluation_context sources layouts tx src) =
   get_tenv (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src)` by
    simp[get_tenv_def, initial_evaluation_context_def, empty_call_txn_def] >>
  drule_all env_scopes_consistent_get_tenv_cong >>
  simp[]
QED

Theorem env_immutables_consistent_context_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  cx1.txn.target = cx2.txn.target /\
  env_immutables_consistent env cx1 st ==>
  env_immutables_consistent env cx2 st
Proof
  simp[env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem initial_env_immutables_consistent_empty_tx[local]:
  env_immutables_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_immutables_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  `get_tenv (initial_evaluation_context sources layouts tx src) =
   get_tenv (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src)` by
    simp[get_tenv_def, initial_evaluation_context_def, empty_call_txn_def] >>
  `!src'. get_module_code
      (initial_evaluation_context sources layouts tx src) src' =
    get_module_code
      (initial_evaluation_context sources layouts
        (empty_call_txn with target := tx.target) src) src'` by
    simp[get_module_code_def, initial_evaluation_context_def,
         empty_call_txn_def] >>
  `(initial_evaluation_context sources layouts tx src).txn.target =
   (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src).txn.target` by
    simp[initial_evaluation_context_def, empty_call_txn_def] >>
  drule_all env_immutables_consistent_context_cong >>
  simp[]
QED

Theorem initial_env_consistent_empty_tx[local]:
  env_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  rw[env_consistent_def]
  >- (irule initial_env_context_consistent_empty_tx >>
      gvs[env_consistent_def])
  >- (irule initial_env_scopes_consistent_empty_tx >>
      gvs[env_consistent_def])
  >> irule initial_env_immutables_consistent_empty_tx >>
  gvs[env_consistent_def]
QED

Theorem checked_public_getter_post_prefix_body_setup_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  ?exp env_after.
    body = [Return (SOME exp)] /\
    type_stmts (function_entry_env art mods src args) ret body = SOME env_after /\
    context_well_typed
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) /\
    functions_well_typed
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) /\
    env_consistent (function_entry_env art mods src args)
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) st /\
    state_well_typed st /\ accounts_well_typed st.accounts /\
    (!st0. eval_stmts cx body st0 =
       eval_stmts
         (initial_evaluation_context am.sources am.layouts
           (empty_call_txn with target := tx.target) src) body st0)
Proof
  rpt strip_tac >>
  drule checked_public_getter_body_typing_package >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `env_consistent (function_entry_env art mods src args)
     (initial_evaluation_context am.sources am.layouts tx src) st` by
    (rw[env_consistent_def]
     >- (irule env_context_consistent_same_static_maps >>
         qexists `artifact_env art mods src` >>
         rpt (conj_tac >-
           simp[function_entry_env_def, artifact_env_def,
                FOLDL_extend_local_args_static, get_tenv_def,
                initial_evaluation_context_def]) >>
         irule check_contract_env_context_consistent_initial_src >> simp[])
     >- (`(st with scopes := [scope]) = st` by
           gvs[evaluation_state_component_equality] >>
         pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
         irule bind_arguments_env_scopes_consistent >>
         qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
         gvs[function_entry_env_def, get_tenv_def,
             initial_evaluation_context_def] >>
         metis_tac[])
     >- (gvs[env_immutables_consistent_def, function_entry_env_def,
              artifact_env_def, FOLDL_extend_local_args_static] >> rw[] >>
         qpat_x_assum
           `immutables_ready _ _
              (initial_evaluation_context am.sources am.layouts tx src) _`
           mp_tac >>
         simp[immutables_ready_def] >> strip_tac >>
         metis_tac[])) >>
  `getter_context_equiv
     (initial_evaluation_context am.sources am.layouts tx src)
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    simp[getter_context_equiv_initial_empty_tx] >>
  drule_all selected_public_getter_body_eval_context_equiv >> strip_tac >>
  gvs[] >>
  `!st0. eval_stmts
      (initial_evaluation_context am.sources am.layouts tx src)
      [Return (SOME exp)] st0 =
    eval_stmts
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src)
      [Return (SOME exp)] st0` by
    (gen_tac >> AP_THM_TAC >>
     metis_tac[getter_context_equiv_eval_single_Return]) >>
  `context_well_typed
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    simp[context_well_typed_def, initial_evaluation_context_def,
         empty_call_txn_def] >>
  `functions_well_typed
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  `env_consistent (function_entry_env art mods src args)
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src) st` by
    (drule initial_env_consistent_empty_tx >> simp[]) >>
  simp[]
QED

Theorem checked_public_getter_post_prefix_body_execution_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_stmts cx body st) /\
  (!v st'. eval_stmts cx body st = (INR (ReturnException v),st') ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv v)
Proof
  strip_tac >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >>
  strip_tac >>
  `call_evaluation_safe
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)
     (int_calls_stmts body)` by (
    `int_calls_stmts body = []` by
      metis_tac[selected_public_getter_body_int_calls_empty] >>
    pop_assum SUBST1_TAC >>
    `ALOOKUP am.sources tx.target = SOME mods` by
      gvs[checked_contract_runtime_ready_def] >>
    `(initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) =
     ((initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) with
       stk := [(src,"")])` by
      simp[initial_evaluation_context_def, empty_call_txn_def] >>
    pop_assum SUBST1_TAC >>
    irule (INST_TYPE [``:'a`` |-> ``:num``]
      checked_contract_call_evaluation_safe_singleton) >>
    qexistsl [`art`, `am.layouts`, `mods`] >>
    simp[initial_evaluation_context_def, empty_call_txn_def,
         calls_follow_call_graph_def]) >>
  `no_type_error_eval
     (eval_stmts
       (initial_evaluation_context am.sources am.layouts
         (empty_call_txn with target := tx.target) src) body st)` by
    metis_tac[eval_stmts_no_type_error] >>
  `no_type_error_eval (eval_stmts cx body st)` by metis_tac[] >>
  `!rv rst. eval_stmts cx body st = (INR (ReturnException rv),rst) ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv rv` by
    (qx_gen_tac `rv` >> qx_gen_tac `rst` >> strip_tac >>
     `eval_stmts
        (initial_evaluation_context am.sources am.layouts
          (empty_call_txn with target := tx.target) src) body st =
        (INR (ReturnException rv),rst)` by metis_tac[] >>
     `state_well_typed rst /\
      stmt_error_ok (function_entry_env art mods src args) ret
        (INR (ReturnException rv))` by
       (irule eval_stmts_type_preservation_exception >>
        qexistsl
          [`initial_evaluation_context am.sources am.layouts
              (empty_call_txn with target := tx.target) src`,
           `env_after`, `body`, `st`] >>
        simp[]) >>
     gvs[vyperTypeStmtResultTheory.stmt_error_ok_def,
         vyperTypeStmtResultTheory.return_exception_typed_def,
         vyperTypeExprSoundnessTheory.value_runtime_typed_def,
         function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static]) >>
  simp[]
QED

Theorem checked_public_getter_body_preserves_machine_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >>
  strip_tac >>
  `int_calls_stmts body = []` by
    metis_tac[selected_public_getter_body_int_calls_empty] >>
  `eval_stmts
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) body st = (res,st')` by
    metis_tac[] >>
  `call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) []` by (
    `ALOOKUP am.sources tx.target = SOME mods` by
      gvs[checked_contract_runtime_ready_def] >>
    `(initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) =
     ((initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) with
       stk := [(src,"")])` by
      simp[initial_evaluation_context_def, empty_call_txn_def] >>
    pop_assum SUBST1_TAC >>
    irule (INST_TYPE [``:'a`` |-> ``:num``]
      checked_contract_call_evaluation_safe_singleton) >>
    qexistsl [`art`, `am.layouts`, `mods`] >>
    simp[initial_evaluation_context_def, empty_call_txn_def,
         calls_follow_call_graph_def]) >>
  irule eval_stmts_preserves_state_and_accounts_well_typed >>
  qexistsl
    [`initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src`,
     `function_entry_env art mods src args`, `env_after`, `res`, `ret`,
     `body`, `st`] >>
  simp[]
QED


Theorem checked_public_getter_post_prefix_body_return_typed_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (INR (ReturnException v),st') ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  rpt strip_tac >>
  drule_all checked_public_getter_post_prefix_body_execution_selected >>
  metis_tac[]
QED

Theorem checked_public_getter_initial_body_execution_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval (eval_stmts cx body
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)) /\
  (!v st'. eval_stmts cx body
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) =
      (INR (ReturnException v),st') ==>
    ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
             value_has_type ret_tv v)
Proof
  strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `accounts_well_typed
     (initial_state am [scope] with <|outcomes := orc; requests := rqs|>).accounts` by
    (simp[] >> metis_tac[initial_state_accounts_well_typed_simple]) >>
  `state_well_typed
     (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` by
    (simp[] >> metis_tac[initial_state_single_scope_well_typed_simple]) >>
  `(initial_state am [scope] with <|outcomes := orc; requests := rqs|>).scopes = [scope]` by
    simp[initial_state_def] >>
  `(initial_state am [scope] with <|outcomes := orc; requests := rqs|>).immutables = am.immutables` by
    simp[initial_state_def] >>
  drule_all checked_public_getter_post_prefix_body_execution_selected >>
  simp[]
QED

Theorem call_external_function_exact_selected_getter_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret = (res,am',rqs) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `no_type_error_eval (eval_stmts cx body (initial_state am [scope] with <|outcomes := orc; requests := []|>)) /\
   (!v st'. eval_stmts cx body (initial_state am [scope] with <|outcomes := orc; requests := []|>) =
       (INR (ReturnException v),st') ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv v)` by
    (drule_all checked_public_getter_initial_body_execution_selected >>
     disch_then (qspecl_then [`[]`, `orc`] mp_tac) >>
     simp[initial_state_def]) >>
  `nr = F /\ mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         gvs[external_getter_tuple_def]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
              (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q` >> gvs[return_def, raise_def]
  >- (`r = initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>` by
        (qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
         rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
            assert_def, return_def, raise_def] >>
         gvs[AllCaseEqs(), return_def, raise_def]) >>
      gvs[set_scopes_def, return_def, initial_state_def] >>
      strip_tac >>
      Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                  [Return (SOME exp)] (initial_state am [scope] with <|outcomes := orc; requests := []|>)` >>
      Cases_on `q` >>
      gvs[initial_evaluation_context_def, initial_state_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >>
      gvs[initial_evaluation_context_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def,
          vyperTypingTheory.safe_cast_well_typed] >>
      rpt strip_tac >> gvs[vyperTypingTheory.safe_cast_well_typed]) >>
  qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem bind_arguments_success_mem_zip_safe_cast:
  !tenv params vals scope id ty raw.
    bind_arguments tenv params vals = SOME scope /\
    MEM ((id,ty),raw) (ZIP (params, vals)) ==>
    ?tv cast_v.
      evaluate_type tenv ty = SOME tv /\
      safe_cast tv raw = SOME cast_v
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem MEM_ZIP_FST[local]:
  !xs ys x y. MEM (x,y) (ZIP (xs,ys)) ==> MEM x xs
Proof
  Induct >> Cases_on `ys` >> rw[ZIP_def] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem bind_arguments_success_flookup_safe_cast:
  !tenv params vals scope id ty raw sv.
    bind_arguments tenv params vals = SOME scope /\
    ALL_DISTINCT (MAP FST params) /\
    MEM ((id,ty),raw) (ZIP (params, vals)) /\
    FLOOKUP scope id = SOME sv ==>
      sv.assignable /\
      ?tv.
        evaluate_type tenv ty = SOME tv /\
        safe_cast tv raw = SOME sv.value /\
        sv.type = tv
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE, MEM_MAP] >>
  gvs[] >>
  imp_res_tac MEM_ZIP_FST >>
  gvs[] >>
  first_x_assum drule >>
  disch_then (qspec_then `sv` mp_tac) >>
  simp[]
QED

Theorem checked_explicit_external_body_no_control_escape_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  stmts_no_control_escape body
Proof
  rpt strip_tac >>
  `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl [`tx.function_name`, `raw`, `External`] >> simp[]) >>
  gvs[check_function_body_def]
QED

Theorem checked_public_getter_body_no_control_escape_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  stmts_no_control_escape body
Proof
  rpt strip_tac >>
  `getter_context_equiv
     (initial_evaluation_context am.sources am.layouts tx src)
     (initial_evaluation_context am.sources am.layouts tx src)` by
    simp[getter_context_equiv_def] >>
  drule_all selected_public_getter_body_eval_context_equiv >>
  strip_tac >>
  gvs[stmt_no_control_escape_def]
QED


Theorem lookup_exported_function_checked_cases_current:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx src) am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw.
     MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
  (?decl.
     MEM decl ts /\
     is_public_getter_decl tx.function_name decl /\
     external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  metis_tac[lookup_exported_function_checked_cases_selected]
QED


Theorem send_call_value_preserves_scopes[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem call_lock_action_preserves_scopes[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready[local]:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env] with <|outcomes := orc; requests := rqs|>) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem acquire_nonreentrant_lock_accounts[local]:
  acquire_nonreentrant_lock target slot ro st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED


Theorem checked_explicit_external_body_setup:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_consistent env_body cx st /\
    context_well_typed cx /\
    functions_well_typed cx /\
    state_well_typed st /\
    accounts_well_typed st.accounts
Proof
  strip_tac >> gvs[checked_contract_runtime_ready_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `functions_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `External <> Deploy` by simp[] >>
  drule_all checked_function_body_typing_package >>
  strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >>
      simp[])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >>
      rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >>
      strip_tac >>
      first_x_assum drule_all >>
      simp[] >>
      strip_tac >>
      first_x_assum (qspecl_then [`id_str`, `tv`, `v`] mp_tac) >>
      simp[])
QED


Theorem checked_explicit_external_body_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_x_assum `cx = _` SUBST1_TAC >>
     gvs[checked_contract_runtime_ready_def] >>
     drule_all checked_explicit_external_body_call_evaluation_safe >>
     simp[]) >>
  drule_all eval_stmts_no_type_error >>
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED



Theorem checked_explicit_external_body_preserves_machine_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_x_assum `cx = _` SUBST1_TAC >>
     gvs[checked_contract_runtime_ready_def] >>
     drule_all checked_explicit_external_body_call_evaluation_safe >>
     simp[]) >>
  irule eval_stmts_preserves_state_and_accounts_well_typed >>
  qexistsl [`cx`, `env_body`, `env_after`, `res`, `ret`, `body`, `st`] >>
  simp[]
QED


Theorem call_external_function_selected_explicit_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function orc am cx nr mut ts mods args dflts tx.args body ret = (res,am',rqs) ==>
  no_type_error_result res
Proof
  metis_tac[call_external_function_exact_selected_no_type_error_c53]
QED


Theorem call_external_function_selected_getter_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function orc am cx nr mut ts mods args dflts tx.args body ret = (res,am',rqs) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `dflts = []` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         gvs[external_getter_tuple_def]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  Cases_on `bind_arguments (type_env_all_modules mods) args tx.args`
  >- (qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[call_external_function_def, initial_evaluation_context_def,
           bind_def, ignore_bind_def, raise_def] >>
      IF_CASES_TAC >- simp[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
        (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
      mp_tac (Q.INST [`mut` |-> `mut`, `cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
        `st` |-> `initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>`]
        send_call_value_no_type_error_c53) >>
      Cases_on `q` >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      strip_tac >> drule external_entry_send_no_control >>
      strip_tac >> Cases_on `y` >> gvs[no_control_exc_def] >> rpt strip_tac >> gvs[]) >>
  metis_tac[call_external_function_exact_selected_getter_no_type_error_c53]
QED


(* ===== Checked external call no-TypeError ===== *)

Theorem checked_call_external_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external orc am tx = (res,am',rqs) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `!ts. ALOOKUP mods (find_function_module am tx.target tx.function_name) = SOME ts ==>
        module_allocated am.layouts tx.target
          (find_function_module am tx.target tx.function_name) ts` by
    metis_tac[checked_contract_runtime_ready_module_allocated] >>
  qpat_x_assum `call_external orc am tx = (res,am',rqs)` mp_tac >>
  simp[Once call_external_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(),
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def, get_self_code_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  `(?raw.
      MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl.
      MEM decl ts /\
      is_public_getter_decl tx.function_name decl /\
      external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
        SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `ALOOKUP all_mods (find_function_module am tx.target tx.function_name) =
   SOME ts` by
    gvs[get_module_code_def, initial_evaluation_context_def] >>
  `checked_contract_runtime_ready art all_mods am tx` by
    simp[checked_contract_runtime_ready_def] >>
  `no_type_error_result ((INR v7):value + vyperState$exception)` by
    (FIRST
       [metis_tac[call_external_function_selected_explicit_raw_args_no_type_error_c53],
        metis_tac[call_external_function_selected_getter_raw_args_no_type_error_c53]]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED






(* ===== Checked external call no escaping loop control ===== *)

Theorem checked_call_external_no_loop_control:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external orc am tx = (INR exc,am',rqs) ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  rpt gen_tac >> strip_tac >>
  `!ts. ALOOKUP mods (find_function_module am tx.target tx.function_name) = SOME ts ==>
        module_allocated am.layouts tx.target
          (find_function_module am tx.target tx.function_name) ts` by
    metis_tac[checked_contract_runtime_ready_module_allocated] >>
  qpat_x_assum `call_external orc am tx = (INR exc,am',rqs)` mp_tac >>
  simp[Once call_external_def] >>
  gvs[AllCaseEqs()] >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def, get_self_code_def] >>
  TRY (Cases_on `exc` >> gvs[] >> NO_TAC) >>
  `(?raw.
      MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl.
      MEM decl ts /\
      is_public_getter_decl tx.function_name decl /\
      external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
        SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >> simp[] >> metis_tac[]) >>
  gvs[]
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_explicit_external_body_no_control_escape_selected])
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_public_getter_body_no_control_escape_selected])
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_explicit_external_body_no_control_escape_selected]) >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[call_external_function_no_loop_control_c53,
            checked_public_getter_body_no_control_escape_selected]
QED

(* Deployment and checked-entry proofs must be closed kernel theorems. *)
val () = List.app
  (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("contract soundness proof is not closed: " ^ name)
    end)
  (DB.thms "vyperTypeContractSoundness");
