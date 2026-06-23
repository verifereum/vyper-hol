(*
 * Final checked-contract type-soundness theorems.
 *
 * This theory owns the public transaction/runtime-readiness predicates and the
 * final deployment/readiness and checked external-call no-TypeError theorems.
 *)

Theory vyperTypeContractSoundness
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeContractFunction vyperTypeContractGetter
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Public transaction and runtime-readiness predicates ===== *)

Definition call_tx_well_typed_def:
  call_tx_well_typed tx <=>
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
  evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
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

Definition checked_contract_runtime_ready_def:
  checked_contract_runtime_ready art mods am tx <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
      (initial_evaluation_context am.sources am.layouts tx NONE)
      am.immutables
End

(* checked_call_external_no_type_error is proved near the end of this file,
   after its explicit-function and public-getter branch helpers. *)

(* ===== Deployment establishes runtime immutable readiness ===== *)

Theorem load_contract_success_cases[local]:
  load_contract am tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <| immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps) |>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE) with in_deploy := T)
      nr mut ts mods args dflts tx.args body ret = (INL v, am_ctor) /\
    am_deployed = am_ctor with sources updated_by CONS (tx.target,mods)
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
  Cases_on `call_external_function
      (am with <|immutables updated_by CONS (tx.target,x);
                exports updated_by CONS (tx.target,exps)|>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx NONE)
         with in_deploy := T)
      q' q (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods q'' q''' tx.args r q''''` >>
  gvs[] >>
  Cases_on `q'''''` >> gvs[] >>
  qexists `a` >> simp[]
QED

Theorem call_external_function_deploy_success_evaluate_all_constants[local]:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) ==>
  ?am_c.
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()]
QED

Theorem deployed_check_contract_bare_globals_consistent[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    ?ts.
      get_module_code
        (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx src) src = SOME ts /\
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      is_bare_global_decl id ts /\
      find_var_decl_by_num id ts = NONE /\
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
  TRY (first_x_assum (qspecl_then [`acc |+ (string_to_num s,(tv,v))`,`cenv`] mp_tac) >>
       simp[FLOOKUP_UPDATE] >> NO_TAC) >>
  first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[]
QED


Theorem constants_env_head_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src)
    ((VariableDecl vis (Constant e) id ty init)::ts))) /\
  constants_env cx am addr src
    ((VariableDecl vis (Constant e) id ty init)::ts) acc = SOME cenv ==>
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
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
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
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

Theorem evaluate_all_constants_preserves_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx am addr mods = SOME am_c /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- (rw[evaluate_all_constants_def] >> gvs[]) >>
  gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum irule >>
  simp[] >>
  qexists `merge_constants addr h0 cenv am` >>
  simp[] >>
  irule merge_constants_preserves_lookup_not_source >>
  simp[]
QED
Theorem evaluate_all_constants_preserves_merged_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx (merge_constants addr src cenv am) addr mods = SOME am_c /\
  FLOOKUP cenv id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  rw[] >>
  drule evaluate_all_constants_preserves_lookup_not_source >>
  disch_then drule >>
  disch_then irule >>
  simp[merge_constants_def, get_source_immutables_set_same,
       empty_immutables_def, FLOOKUP_FUNION]
QED

Theorem evaluate_all_constants_contains_constant_type[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  ?tv v. FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    (string_to_num id) = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def, alistTheory.ALOOKUP_def] >>
  gvs[AllCaseEqs()] >-
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel h0) h1))` by
       gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     drule constants_env_contains_constant_type >>
     disch_then drule >>
     disch_then drule >>
     strip_tac >>
     `FLOOKUP (get_source_immutables h0
        (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
        (string_to_num id) = SOME (tv,v)` by
       (gvs[contract_namespaces_ok_def] >>
        drule evaluate_all_constants_preserves_merged_lookup_not_source >>
        disch_then drule >>
        disch_then drule >>
        simp[]) >>
     qexistsl [`tv`,`v`] >>
     gvs[set_current_module_def, get_tenv_def]) >>
  first_x_assum irule >>
  gvs[contract_namespaces_ok_def] >>
  conj_tac >- metis_tac[] >>
  gvs[contract_keys_def, ALL_DISTINCT_APPEND]
QED

Theorem contract_toplevel_vtype_key_MEM_Variable[local]:
  MEM (src,ts) mods /\ MEM (VariableDecl vis mut id ty init) ts ==>
  MEM ((src : num option),string_to_num id)
    (contract_keys toplevel_vtype_keys_toplevel mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)` >> simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED
Theorem module_toplevel_vtype_key_MEM_Variable_any[local]:
  MEM (VariableDecl vis mut id ty init) ts ==>
  MEM (src,string_to_num id)
    (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,string_to_num id)]` >> simp[] >>
  qexists `VariableDecl vis mut id ty init` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED


Theorem module_immutable_constant_string_nums_distinct[local]:
  !src ts visI idI tyI initI visC e idC tyC slotC.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visC (Constant e) idC tyC slotC) ts ==>
    string_to_num idI <> string_to_num idC
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED
Theorem module_immutable_string_num_type_unique[local]:
  !src ts visI idI tyI initI visJ idJ tyJ initJ.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visJ Immutable idJ tyJ initJ) ts /\
    string_to_num idJ = string_to_num idI ==>
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
    mods (FEMPTY |+ ((src,string_to_num id_str), ty))
Proof
  rw[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE] >>
  gvs[] >>
  rename1 `ALOOKUP mods src0 = SOME ts` >>
  `MEM (src0,ts) mods` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `ALOOKUP mods src0 = SOME ts'` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src0) ts))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
  irule module_immutable_constant_string_nums_distinct >>
  qexistsl [`e`,`init`,`slot`,`src0`,`ts`,`typ`,`ty`,`vis'`,`vis`] >>
  simp[]
QED

Theorem deploy_constants_setup_bare_globals_ready[local]:
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
      >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
            (irule initial_immutables_contains_decl >>
             qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
             simp[] >>
             conj_tac
             >- (irule find_var_decl_by_num_NONE_Immutable >>
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
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
          gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
          gvs[] >>
          metis_tac[constants_do_not_clobber_single_immutable]) >>
      metis_tac[evaluate_all_constants_contains_constant_type, IS_SOME_EXISTS]) >>
  rw[] >>
  `(?ts vis id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis Immutable id_str ty init) ts /\
      id = string_to_num id_str) \/
   (?ts vis e id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
      id = string_to_num id_str)` by
    metis_tac[build_contract_type_artifact_bare_globals_sound] >>
  gvs[]
  >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
        (irule initial_immutables_contains_decl >>
         qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
         simp[] >>
         conj_tac
         >- (irule find_var_decl_by_num_NONE_Immutable >>
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
         (string_to_num id_str) = SOME x` by
        (irule evaluate_all_constants_preserves_bare_global_lookup_type >>
         qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
         gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
         metis_tac[constants_do_not_clobber_single_immutable]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
         metis_tac[alistTheory.ALOOKUP_MEM]) >>
      `is_immutable_decl (string_to_num id_str) ts` by
        metis_tac[is_immutable_decl_MEM] >>
      irule initial_immutables_all_bare_global_type >>
      qexistsl [`string_to_num id_str`, `imms`, `mods`, `src`, `ts`, `v`] >>
      gvs[] >>
      metis_tac[module_immutable_string_num_type_unique]) >>
  drule evaluate_all_constants_contains_constant_type >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
      gvs[]
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
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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
        NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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

Theorem preserves_tv_initial_immutables_lookup[local]:
  !cx am_c env st src id tv x.
    preserves_tv cx (initial_state am_c [env]) st ==>
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
  preserves_tv cx (initial_state am_c [env]) st_body /\
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
  drule preserves_tv_initial_immutables_lookup >>
  disch_then drule >>
  rw[] >>
  metis_tac[]
QED

Theorem call_external_function_deploy_normal_success_lookup_transport[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INL (),st_body)) /\
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
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_deploy_return_success_lookup_transport[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INR (ReturnException v_ret),st_body)) /\
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
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_success_result_cases[local]:
  (\(res,st). (res,st))
    (case body_res of
       (INL (), st) =>
         (case unlock st of
            (INL u, st') => (INL NoneV, abstract_machine_from_state srcs exps layouts st')
          | (INR e, st') => (INR e, am))
     | (INR (ReturnException v_ret), st) =>
         (case unlock st of
            (INL u, st') =>
              (case evaluate_type tenv ret of
                 NONE => (INR (Error (RuntimeError "eval ret")), am)
               | SOME tv =>
                   case safe_cast tv v_ret of
                     NONE => (INR (Error (RuntimeError "ext cast ret")), am)
                   | SOME v_cast =>
                       (INL v_cast, abstract_machine_from_state srcs exps layouts st'))
          | (INR e, st') => (INR e, am))
     | (INR e, st) => (INR e, am)) = (INL v, am_out) ==>
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

Theorem call_external_function_deploy_success_cases[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  ?dflt_vs env.
    evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
    bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME env /\
    ((?st_body st_unlocked u.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INL (), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked) \/
     (?v_ret st_body st_unlocked u tv v_cast.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INR (ReturnException v_ret), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        evaluate_type (type_env_all_modules all_mods) ret = SOME tv /\
        safe_cast tv v_ret = SOME v_cast /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked))
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()] >>
  drule call_external_function_success_result_cases >>
  simp[]
QED

Theorem call_external_function_deploy_success_preserves_immutable_type_tags_from_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[] >-
    (irule call_external_function_deploy_normal_success_lookup_transport >>
     qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `x`] >>
     simp[]) >>
  irule call_external_function_deploy_return_success_lookup_transport >>
  qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `v_ret`, `x`] >>
  simp[]
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
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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
  first_x_assum (qspec_then `addr` mp_tac) >> decide_tac
QED

Theorem send_call_value_no_type_error_c53[local]:
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

Theorem send_call_value_accounts_well_typed_c53[local]:
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

Theorem call_lock_action_preserves_accounts_c53[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready_c53[local]:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
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

Theorem call_lock_action_no_type_error_c53[local]:
  no_type_error_eval
    ((if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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

Theorem unlock_action_no_type_error_c53[local]:

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

Theorem call_lock_send_eval_prefix_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       send_call_value mut cx;
       eval_stmts cx body
     od (initial_state am [scope]))
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `ALL_DISTINCT (MAP (string_to_num o FST) args)` by
    (`check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
       metis_tac[check_contract_function_body_MEM] >>
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
                 NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock
                   (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (`r''.scopes = [scope] /\ r''.immutables = am.immutables /\ state_well_typed r''` by
            (irule call_lock_send_prefix_body_state_ready_c53 >>
             simp[bind_def, ignore_bind_def] >>
             qexistsl [`initial_evaluation_context am.sources am.layouts tx src`, `mut`, `nr`] >>
             simp[]) >>
          `accounts_well_typed r.accounts` by
            (imp_res_tac call_lock_action_preserves_accounts_c53 >>
             gvs[initial_state_accounts_well_typed]) >>
          `accounts_well_typed r''.accounts` by
            (imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_eval_def] >>
          irule checked_explicit_external_post_prefix_body_no_type_error_selected >>
          simp[] >>
          qexistsl [`am`, `args`, `art`, `dflts`, `mods`, `mut`, `nr`, `raw`,
                    `ret`, `src`, `ts`, `tx`, `vals`] >>
          simp[]) >>
      `no_type_error_eval
         (send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r)` by
        simp[send_call_value_no_type_error_c53] >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]) >>
  `no_type_error_eval
     ((if nr then
         case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
           NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock
             (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
             (mut = View \/ mut = Pure)
       else return ()) (initial_state am [scope]))` by
    simp[call_lock_action_no_type_error_c53] >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED

Theorem call_external_function_exact_selected_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `no_type_error_eval
     (do
        (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock
               (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
               (mut = View \/ mut = Pure)
         else return ());
        send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
        eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
      od (initial_state am [scope]))` by
    metis_tac[call_lock_send_eval_prefix_no_type_error_c53,
              checked_contract_runtime_ready_def] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      initial_evaluation_context_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  qpat_x_assum `!msg. FST _ <> INR (Error (TypeError msg))`
    (qspec_then `msg` mp_tac) >>
  qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[return_def, raise_def,
        vyperTypeExprSoundnessTheory.no_type_error_eval_def,
        vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >>
  qpat_x_assum
    `(if nr /\ mut <> View /\ mut <> Pure then
        case lookup_nonreentrant_slot am.layouts tx.target of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock tx.target slot
      else return ()) r = (INR y,r'')` mp_tac >>
  Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
  Cases_on `nr` >>
  Cases_on `mut` >>
  gvs[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
      get_transient_storage_def, update_transient_def,
      return_def, raise_def, assert_def, check_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_explicit_external_entry_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  call_external_function am (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (res,am') ==>
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
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (res,st')) ==>
  preserves_immutables_dom cx (initial_state am_c [env]) st'
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

Theorem call_external_function_deploy_success_final_lookup_source_exists_in_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
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
  >- (imp_res_tac call_body_prefix_preserves_immutables_dom >>
      `st_unlocked.immutables = st_body.immutables` by
        (Cases_on `nr` >> gvs[return_def] >>
         Cases_on `mut = View` >> gvs[return_def] >>
         Cases_on `mut = Pure` >> gvs[return_def] >>
         Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
         imp_res_tac release_nonreentrant_lock_immutables) >>
      gvs[abstract_machine_from_state_def] >>
      irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]) >>
  imp_res_tac call_body_prefix_preserves_immutables_dom >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `nr` >> gvs[return_def] >>
     Cases_on `mut = View` >> gvs[return_def] >>
     Cases_on `mut = Pure` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  gvs[abstract_machine_from_state_def] >>
  irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]
QED

Theorem deploy_call_success_transports_bare_global_readiness_clause[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
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
  call_external_function am cx nr mut ts all_mods args dflts vals body ret = (INL v_out,am_out) /\
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
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor) /\
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
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor)` by
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
     `id`, `mut`, `nr`, `ret`, `src`, `ts`, `v`, `v'`, `deploy_tx.args`] >>
  gvs[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`src'`,`id'`,`ty'`,`tv'`,`v''`] mp_tac) >>
  simp[]
QED

Theorem evaluate_all_constants_preserves_layouts[local]:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.layouts = am.layouts
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  Cases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs(), merge_constants_def] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_deploy_success_preserves_layouts[local]:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out am_c.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
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

Theorem load_contract_success_constructor_constants_context[local]:
  load_contract am deploy_tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor am_c.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE deploy_tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      nr mut ts mods args dflts deploy_tx.args body ret = (INL v, am_ctor) /\
    evaluate_all_constants
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      deploy_tx.target mods = SOME am_c /\
    am_ctor.layouts = am.layouts /\
    am_deployed = am_ctor with sources updated_by CONS (deploy_tx.target,mods)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  qspecl_then
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
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
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
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
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
    deploy_tx.args body ret = (INL v',am_ctor) /\
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
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
     deploy_tx.args body ret = (INL v',am_ctor)` by
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
  load_contract am deploy_tx mods exps = INL am_deployed /\
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
     `dflts`, `exps`, `id`, `mut`, `nr`, `ret`, `src`, `v`, `v'`] >>
  gvs[]
QED

Theorem deployed_toplevel_vtypes_immutables_ready_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
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
       find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
       typ = ty) /\
    (!is_transient kt vt id_str.
       find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
       F) /\
    (find_var_decl_by_num id ts = NONE ==>
     !tv v.
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
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
        find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
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
        find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
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
  !cx am nr mut ts all_mods args dflts vals body ret v am_out am_c src id.
    cx.in_deploy /\
    call_external_function am cx nr mut ts all_mods args dflts vals body ret =
      (INL v, am_out) /\
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
  load_contract am deploy_tx mods exps = INL am_deployed /\
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
  qspecl_then [`(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
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
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  immutables_ready call_art.cta_bare_globals call_art.cta_toplevel_vtypes
    (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE)
    am_deployed.immutables
Proof
  rw[immutables_ready_def]
  >- (simp[initial_evaluation_context_def] >>
      irule load_contract_deployed_bare_globals_immutables_ready_exists_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `mods`, `ty`] >>
      gvs[])
  >- (irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `v`] >>
      gvs[initial_evaluation_context_def])
  >- (irule (cj 1 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `mods`, `src`, `ts`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >- (strip_tac >>
      irule (cj 2 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `kt`, `mods`, `src`, `ts`, `ty`, `vt`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >> irule (cj 3 deployed_toplevel_vtypes_immutables_ready_clause) >>
     qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `ts`, `v`] >>
     simp[] >>
     rpt strip_tac >>
     drule load_contract_deployed_bare_globals_immutables_ready_clause >>
     simp[] >>
     disch_then drule >>
     simp[] >>
     disch_then (qspecl_then [`src'`, `id'`, `ty'`, `tv'`, `v'`] mp_tac) >>
     simp[initial_evaluation_context_def] >>
     strip_tac >>
     gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_checked_contract_runtime_ready:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME art /\
  call_tx.target = deploy_tx.target ==>
  checked_contract_runtime_ready art mods am_deployed call_tx
Proof
  rw[checked_contract_runtime_ready_def]
  >- (drule load_contract_success_cases >> strip_tac >> gvs[])
  >> irule load_contract_establishes_immutables_ready
  >> qexistsl [`am`, `deploy_tx`, `exps`, `mods`]
  >> simp[]
QED

Theorem generated_array_getter_recursive_step_no_type_error_materialisable[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type vt) (SUC n) = (args',ret,exp) /\
  bind_arguments (get_tenv cx) ((num_to_dec_string n,BaseT (UintT 256))::args') vals = SOME scope /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV inner_tv b) bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV inner_tv b) bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  (case step_res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv b) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv b))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) vt = SOME inner_tv` by
    (qpat_x_assum `evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b)` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `(!id typ id' typ'.
      MEM (id,typ) ((num_to_dec_string n,BaseT (UintT 256))::args') /\
      MEM (id',typ') ((num_to_dec_string n,BaseT (UintT 256))::args') /\
      string_to_num id' = string_to_num id ==> typ' = typ)` by
    (rpt strip_tac >> gvs[] >>
     imp_res_tac string_to_num_eq_imp >> gvs[] >>
     TRY (metis_tac[build_getter_args_no_current_name]) >>
     metis_tac[build_getter_args_num_unique]) >>
  irule generated_array_subscript_step_NoneTV_nested_carrier >>
  simp[evaluate_type_def] >>
  conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
  >- (qexistsl [`am`, `((num_to_dec_string n,BaseT (UintT 256))::args')`, `bd`,
                `cx`, `e`, `n`, `scope`, `st1`, `step_st`, `get_tenv cx`, `tvl`, `vals`] >>
      simp[] >> rpt strip_tac >> simp[] >>
      imp_res_tac string_to_num_eq_imp >> simp[] >>
      TRY (metis_tac[build_getter_args_no_current_name]) >>
      metis_tac[build_getter_args_num_unique])
  >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
  >- (qexistsl [`am`, `((num_to_dec_string n,BaseT (UintT 256))::args')`, `bd`,
                `cx`, `e`, `n`, `scope`, `st1`, `step_st`, `get_tenv cx`, `tvl`, `vals`] >>
      simp[] >> rpt strip_tac >> simp[] >>
      imp_res_tac string_to_num_eq_imp >> simp[] >>
      TRY (metis_tac[build_getter_args_no_current_name]) >>
      metis_tac[build_getter_args_num_unique])
QED

Theorem generated_array_getter_recursive_step_no_type_error_materialisable_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type vt) (SUC n) = (args',ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV inner_tv b) bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV inner_tv b) bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  (case step_res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv b) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv b))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) vt = SOME inner_tv` by
    (qpat_x_assum `evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b)` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  irule generated_array_subscript_step_NoneTV_nested_carrier >>
  simp[] >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
QED

Theorem generated_array_subscript_base_error_no_type_error[local]:
  eval_expr cx e (initial_state am [scope]) = (INR err, st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx (Subscript NoneT e idx) (initial_state am [scope]) = (step_res, step_st) ==>
  no_type_error_result step_res /\
  (case step_res of INR _ => T | INL _ => T)
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript NoneT e idx) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `no_type_error_result (INR err)` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem build_getter_ArrayT_tail_all_args[local]:
  build_getter e kt (Type (ArrayT vt b)) n = (args,ret,exp) /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) ==>
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type vt) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,kt)::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args) /\
    MEM (num_to_dec_string n,kt) all_args
Proof
  rpt strip_tac >>
  qabbrev_tac `tail = build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (BaseT (UintT 256)) (Type vt) (SUC n)` >>
  PairCases_on `tail` >>
  qexistsl [`tail0`, `tail1`, `tail2`] >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, is_ArrayT_def, ArrayT_type_def] >>
  strip_tac >> gvs[] >>
  metis_tac[]
QED


Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient[local]:
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >> Cases_on `base_res` >> gvs[]
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error]
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error] >>
  metis_tac[generated_array_subscript_base_error_no_type_error]
QED
Theorem generated_array_subscript_step_NoneTV_materialisable_ambient[local]:
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt strip_tac
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient] >>
  Cases_on `base_res` >> gvs[]
  >- metis_tac[cj 2 generated_array_subscript_step_NoneTV_materialisable]
  >- metis_tac[cj 2 generated_array_subscript_step_NoneTV_materialisable] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_tail_IH_package_ambient[local]:
  build_getter e (BaseT (UintT 256)) (Type (ArrayT vt b)) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV tv b) /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type vt) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,BaseT (UintT 256))::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all build_getter_ArrayT_tail_all_args >> strip_tac >> gvs[] >>
  `MEM (num_to_dec_string n,BaseT (UintT 256)) all_args` by metis_tac[] >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient] >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  Cases_on `base_res` >> gvs[]
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[] >> metis_tac[]) 
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_tail_IH_package_ambient_ArrayT[local]:
  build_getter e (BaseT (UintT 256)) (Type (ArrayT t b)) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,BaseT (UintT 256))::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT t b) = SOME (ArrayTV tv b)` by
    simp[evaluate_type_def] >>
  drule_all generated_array_getter_ArrayT_tail_IH_package_ambient >>
  simp[]
QED

Theorem ArrayT_type_value_type_size_lt[local]:
  is_ArrayT vt ==> value_type_size (Type (ArrayT_type vt)) < value_type_size (Type vt)
Proof
  Cases_on `vt` >> simp[is_ArrayT_def, ArrayT_type_def]
QED

Theorem build_getter_total[local]:
  ?args ret exp. build_getter e kt vt n = (args,ret,exp)
Proof
  Cases_on `build_getter e kt vt n` >> PairCases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem generated_array_getter_ArrayT_step_carrier_shape_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `base_res` >> gvs[]
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)`
      >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[evaluate_type_def] >>
      qexistsl [`all_args`,`am`,`args_tail`,`cx`,`e`,`exp_tail`,`n`,`ret_tail`,
                `scope`,`st1`,`step_st`,`tenv`,`Value (ArrayV av)`,`vals`,`t`] >>
      simp[evaluate_type_def] >> metis_tac[])
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)`
      >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[evaluate_type_def] >>
      qexistsl [`all_args`,`am`,`args_tail`,`cx`,`e`,`exp_tail`,`n`,`ret_tail`,
                `scope`,`st1`,`step_st`,`tenv`,`ArrayRef is_transient slot (ArrayTV tv b) bd`,`vals`,`t`] >>
      simp[evaluate_type_def] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. (id = num_to_dec_string n /\ typ = BaseT (UintT 256) \/ MEM (id,typ) args_tail) ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (num_to_dec_string n, BaseT (UintT 256)) all_args` by metis_tac[] >>
  conj_tac
  >- (drule_all generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient >> simp[]) >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  conj_tac
  >- (drule_all generated_array_getter_ArrayT_step_carrier_shape_ambient >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED


Theorem generated_array_getter_expr_no_type_error_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  completeInduct_on `value_type_size (Type vt)` >>
  rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) (initial_state am [scope])` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `vals`, `scope`, `q`, `r`,
         `res`, `st'`, `cx`, `am`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  drule_all generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient >>
  simp[]
QED

Theorem generated_array_getter_expr_materialisable_shape_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) (initial_state am [scope])` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `vals`, `scope`, `q`, `r`,
         `res`, `st'`, `cx`, `am`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  drule_all generated_array_subscript_step_NoneTV_materialisable_ambient >>
  simp[]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_array_getter_expr_no_type_error_ambient_aux >> simp[])
  >> drule_all generated_array_getter_expr_materialisable_shape_ambient_aux >> simp[]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  irule generated_array_getter_expr_no_type_error_materialisable_ambient_aux >>
  simp[] >> metis_tac[build_getter_args_num_unique]
QED

Theorem build_getter_base_error_no_type_error[local]:
  !e kt vt n args ret exp cx am scope err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e (initial_state am [scope]) = (INR err,st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def]) 
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_materialisable_shape[local]:
  !e kt vt n args ret exp cx am scope err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e (initial_state am [scope]) = (INR err,st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_no_type_error_post_prefix[local]:
  !e kt vt n args ret exp cx st err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e st = (INR err,st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_materialisable_shape_post_prefix[local]:
  !e kt vt n args ret exp cx st err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e st = (INR err,st1) /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED


Theorem generated_array_subscript_step_NoneTV_nested_carrier_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (FIRST [irule generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix,
            irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix)] >>
     gvs[] >> metis_tac[]) >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i) st` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
      Cases_on `evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i)` >>
      gvs[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >>
          gvs[bind_def, return_def, raise_def,
              vyperTypeExprSoundnessTheory.no_type_error_result_def]
          >- (drule_all evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier >>
              strip_tac >> metis_tac[]) >>
          gvs[evaluate_subscript_def, AllCaseEqs()]) >>
      gvs[evaluate_subscript_def, AllCaseEqs()]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) st` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >>
      gvs[bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `x` >> gvs[bind_def, return_def, raise_def,
                               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `y'` >> gvs[bind_def, return_def, raise_def,
                                 vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `r'` >> gvs[bind_def, return_def, raise_def,
                                vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `read_storage_slot cx q q' r'' r` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `q''` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
           strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      TRY (drule_all evaluate_subscript_NoneTV_ArrayRef_nested_carrier >>
           strip_tac >> metis_tac[])) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule check_array_bounds_ArrayRef_error_not_TypeError_getter >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
QED


Theorem generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. (id = num_to_dec_string n /\ typ = BaseT (UintT 256) \/ MEM (id,typ) args_tail) ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e st = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (num_to_dec_string n, BaseT (UintT 256)) all_args` by metis_tac[] >>
  `well_formed_type_value (ArrayTV tv b)` by
    (qsuff_tac `evaluate_type (get_tenv cx) (ArrayT t b) = SOME (ArrayTV tv b)`
     >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
     simp[evaluate_type_def]) >>
  conj_tac
  >- (Cases_on `base_res` >> gvs[]
      >- (irule (cj 1 generated_array_subscript_step_NoneTV_nested_carrier_post_prefix) >> simp[] >> metis_tac[])
      >- (irule (cj 1 generated_array_subscript_step_NoneTV_nested_carrier_post_prefix) >> simp[] >> metis_tac[]) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  conj_tac
  >- (Cases_on `base_res` >> gvs[]
      >- (qsuff_tac `no_type_error_result step_res /\
            (case step_res of
             | INL tvl' =>
                 ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
                  (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
             | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
          irule generated_array_subscript_step_NoneTV_nested_carrier_post_prefix >> simp[] >> metis_tac[])
      >- (qsuff_tac `no_type_error_result step_res /\
            (case step_res of
             | INL tvl' =>
                 ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
                  (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
             | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
          irule generated_array_subscript_step_NoneTV_nested_carrier_post_prefix >> simp[] >> metis_tac[]) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem generated_array_getter_expr_no_type_error_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\ pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\ no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (irule build_getter_total) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `tenv`, `vals`, `scope`, `q`, `st`, `r`,
         `res`, `st'`, `cx`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `base_res` >> gvs[]
  >- (irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `Value (ArrayV av)`,`vals`] >>
      simp[] >> metis_tac[])
  >- (irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `ArrayRef is_transient slot elem_tv bd`,`vals`] >>
      simp[] >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_array_getter_expr_materialisable_shape_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\ pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\ no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (irule build_getter_total) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `tenv`, `vals`, `scope`, `q`, `st`, `r`,
         `res`, `st'`, `cx`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `base_res` >> gvs[]
  >- (irule (cj 2 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `Value (ArrayV av)`,`vals`] >>
      simp[] >> metis_tac[])
  >- (irule (cj 2 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `ArrayRef is_transient slot elem_tv bd`,`vals`] >>
      simp[] >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_array_getter_expr_no_type_error_post_prefix_aux >> simp[]) >>
  drule_all generated_array_getter_expr_materialisable_shape_post_prefix_aux >> simp[]
QED

Theorem generated_hashmap_subscript_step_no_type_error_post_prefix[local]:
  !tenv params vals scope n kt vt cx e st is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  irule Subscript_NoneTV_HashMapRef_no_TypeError >>
  qexistsl [`slot`, `cx`, `is_transient`, `kt`, `entry.value`, `st`, `st2`, `vt`] >>
  simp[]
QED

Theorem generated_hashmap_subscript_step_error_no_type_error_post_prefix[local]:
  !tenv params vals scope n kt vt cx e st is_transient slot st1 err st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INR err,st2) ==>
  no_type_error_result (INR err)
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`,`params`,`vals`,`scope`,`n`,`kt`,`vt`,`cx`,`e`,`st`,
               `is_transient`,`slot`,`st1`,`INR err`,`st2`]
    mp_tac generated_hashmap_subscript_step_no_type_error_post_prefix >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_hashmap_subscript_step_materialisable_post_prefix[local]:
  !tenv params vals scope n kt t cx e st is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type t) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (Type t)),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[return_def, raise_def, bind_def, check_value_type_def,
      assignable_type_def, well_formed_type_def] >>
  TRY (Cases_on `res'` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `y` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `read_storage_slot cx q r r' s''` >>
       Cases_on `q'` >> gvs[return_def, raise_def, bind_def]) >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL (v:value),s'') => (INL (Value v),s'')
                 | (INR (err:vyperState$exception),s'') => (INR err,s'')) = (res,st2)` mp_tac >>
  CASE_TAC >> CASE_TAC >>
  gvs[return_def, raise_def, bind_def, vyperStorageTheory.encode_hashmap_key_def] >>
  TRY (Cases_on `q` >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED



Theorem generated_hashmap_subscript_step_success_carrier_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (HashMapT kt' vt')),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INL tvl,st2) ==>
  ?slot'. tvl = HashMapRef is_transient slot' kt' vt'
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_typed_package_post_prefix[local]:
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) elem_ast /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) elem_ast = SOME elem_tv /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT elem_ast bd_ast))),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INL tvl,step_st) ==>
  ((?av bd. tvl = Value (ArrayV av) /\
            value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient' slot' bd. tvl = ArrayRef is_transient' slot' elem_tv bd))
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `0 < type_slot_size elem_tv /\
            type_slot_size (ArrayTV elem_tv bd_ast) < dimword (:256)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd_ast) st` >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd_ast)` by
    (`evaluate_type (get_tenv cx) (ArrayT elem_ast bd_ast) = SOME (ArrayTV elem_tv bd_ast)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_getter_expr_no_type_error_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                              assignable_type_def, well_formed_type_def,
                              evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
      irule (cj 1 generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux) >>
      qexistsl [`params`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package_post_prefix >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) vtyp` by
        (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
         simp[Once check_value_type_def]) >>
      `no_type_error_result (INR y)` by
        (drule_all generated_hashmap_subscript_step_error_no_type_error_post_prefix >> simp[]) >>
      drule_all build_getter_base_error_no_type_error_post_prefix >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
  `check_value_type (get_tenv cx) vtyp` by
    (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
     simp[Once check_value_type_def]) >>
  `no_type_error_result (INR y)` by
    (drule_all generated_hashmap_subscript_step_error_no_type_error_post_prefix >> simp[]) >>
  drule_all build_getter_base_error_no_type_error_post_prefix >> simp[]
QED

Theorem generated_hashmap_getter_expr_materialisable_shape_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                            assignable_type_def, well_formed_type_def,
                            evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
      irule (cj 2 generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux) >>
      qexistsl [`params`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package_post_prefix >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_materialisable_post_prefix >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      drule_all build_getter_base_error_materialisable_shape_post_prefix >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  drule_all build_getter_base_error_materialisable_shape_post_prefix >> simp[]
QED

Theorem generated_hashmap_getter_expr_no_type_error_materialisable_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_hashmap_getter_expr_no_type_error_post_prefix >> simp[]) >>
  drule_all generated_hashmap_getter_expr_materialisable_shape_post_prefix >> simp[]
QED


Theorem generated_hashmap_getter_expr_no_type_error[local]:
  !e kt vt n args ret exp tenv params vals scope cx am
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                              assignable_type_def, well_formed_type_def,
                              evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (initial_state am [scope])` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_params >>
         simp[]) >>
      irule (cj 1 generated_array_getter_expr_no_type_error_materialisable_ambient_aux) >>
      qexistsl [`params`,`am`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_no_type_error_params >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
              (initial_state am [scope])` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) vtyp` by
        (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
         simp[Once check_value_type_def]) >>
      `no_type_error_result (INR y)` by
        (drule_all generated_hashmap_subscript_step_error_no_type_error_params >> simp[]) >>
      drule_all build_getter_base_error_no_type_error >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
  `check_value_type (get_tenv cx) vtyp` by
    (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
     simp[Once check_value_type_def]) >>
  `no_type_error_result (INR y)` by
    (drule_all generated_hashmap_subscript_step_error_no_type_error_params >> simp[]) >>
  drule_all build_getter_base_error_no_type_error >> simp[]
QED

Theorem generated_public_array_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,fn)) (initial_state am [scope])` >>
  `no_type_error_result q` by
    (qunabbrev_tac `cx` >> metis_tac[checked_scalar_public_getter_eval_no_type_error]) >>
  Cases_on `typ` >> gvs[is_ArrayT_def, ArrayT_type_def, Abbr `cx`] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn (ArrayT t b) init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def] >>
  Cases_on `evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t` >>
  gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
      evaluate_type_def, get_tenv_def, initial_evaluation_context_def] >>
  irule generated_array_getter_expr_no_type_error_materialisable_aux >>
  qexistsl [`am`, `args`, `q`, `initial_evaluation_context am.sources am.layouts tx src`,
            `TopLevelName NoneT (src,fn)`, `x`, `exp`, `0`, `ret`, `scope`,
            `st'`, `r`, `vals`, `t`] >>
  simp[pure_expr_def, expr_type_def, evaluate_type_def,
       get_tenv_def, initial_evaluation_context_def] >>
  Cases_on `q` >> simp[] >>
  `(?av. x' = Value (ArrayV av) /\ value_has_type (ArrayTV x b) (ArrayV av)) \/
   (?is_transient slot. x' = ArrayRef is_transient slot x b)` suffices_by metis_tac[] >>
  irule checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT >>
  simp[get_tenv_def, initial_evaluation_context_def] >>
  goal_assum $ drule_at Any >>
  simp[get_tenv_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) (initial_state am [scope])` >>
  `no_type_error_result q` by
    (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_no_type_error]) >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_no_type_error >>
      qexistsl [`am`, `args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  drule_all build_getter_base_error_no_type_error >> simp[]
QED

Theorem generated_hashmap_subscript_step_materialisable_params[local]:
  !tenv params vals scope n kt t cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type t) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type t)),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[return_def, raise_def, bind_def, check_value_type_def,
      assignable_type_def, well_formed_type_def] >>
  TRY (Cases_on `res'` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `y` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `read_storage_slot cx q r r' s''` >>
       Cases_on `q'` >> gvs[return_def, raise_def, bind_def]) >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL (v:value),s'') => (INL (Value v),s'')
                 | (INR (err:vyperState$exception),s'') => (INR err,s'')) = (res,st2)` mp_tac >>
  CASE_TAC >> CASE_TAC >>
  gvs[return_def, raise_def, bind_def, vyperStorageTheory.encode_hashmap_key_def] >>
  TRY (Cases_on `q` >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem generated_hashmap_getter_expr_materialisable_shape[local]:
  !e kt vt n args ret exp tenv params vals scope cx am
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                            assignable_type_def, well_formed_type_def,
                            evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (initial_state am [scope])` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_params >> simp[]) >>
      irule (cj 2 generated_array_getter_expr_no_type_error_materialisable_ambient_aux) >>
      qexistsl [`params`,`am`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package >>
          simp[] >> metis_tac[]) >>
      metis_tac[]) 
  >- (drule_all generated_hashmap_subscript_step_materialisable_params >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
              (initial_state am [scope])` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      drule_all build_getter_base_error_materialisable_shape >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  drule_all build_getter_base_error_materialisable_shape >> simp[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_public_hashmap_getter_expr_no_type_error >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_materialisable_shape >>
      qexistsl [`am`, `args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  drule_all build_getter_base_error_materialisable_shape >> simp[]
QED

Theorem selected_public_getter_expr_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule (cj 1 generated_public_array_getter_expr_no_type_error_materialisable) >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >> metis_tac[checked_scalar_public_getter_eval_no_type_error]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule generated_public_hashmap_getter_expr_no_type_error >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem selected_public_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule selected_public_getter_expr_no_type_error >> metis_tac[]) >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule (cj 2 generated_public_array_getter_expr_no_type_error_materialisable) >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >>
      drule_all checked_scalar_public_getter_eval_no_type_error_materialisable >> simp[]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule (cj 2 generated_public_hashmap_getter_expr_no_type_error_materialisable) >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem generated_public_array_getter_args_num_unique[local]:
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type t) 0 =
    (args,ret,exp) ==>
  !id typ id' typ'.
    MEM (id,typ) args /\ MEM (id',typ') args /\
    string_to_num id' = string_to_num id ==> typ' = typ
Proof
  metis_tac[build_getter_args_num_unique]
QED

Theorem checked_public_array_TopLevelName_base_result_for_generated_getter_aux[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  st.immutables = am.immutables /\ state_well_typed st /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME x /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (base_res,r) ==>
  no_type_error_result base_res /\
  (case base_res of
     INL tvl =>
       (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV x bd) (ArrayV av)) \/
       (?is_transient slot bd. tvl = ArrayRef is_transient slot x bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
      simp[get_module_code_def, initial_evaluation_context_def] >>
    `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type (ArrayT t b))` by
      (`toplevel_vtypes_complete art.cta_toplevel_vtypes
          (initial_evaluation_context am.sources am.layouts tx src)` by
         (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
       gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
    `check_toplevel_decl am.layouts tx.target mods art src
       (VariableDecl Public mut fn (ArrayT t b) init)` by
      metis_tac[check_contract_toplevel_decl_MEM] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
      (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
       gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
         return_def, raise_def, initial_evaluation_context_def] >>
    Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                          well_formed_type_def]
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts =
           SOME (StorageVarDecl T (ArrayT t b),fn)` by
          metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                    contract_namespaces_ok_module_toplevel_vtype_keys,
                    ALOOKUP_MEM, check_contract_def] >>
        gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
            get_tenv_def, initial_evaluation_context_def] >>
        drule assignable_type_well_formed >> simp[well_formed_type_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
        gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
        imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
        gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    `find_var_decl_by_num (string_to_num fn) ts =
       SOME (StorageVarDecl F (ArrayT t b),fn)` by
      metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
                contract_namespaces_ok_module_toplevel_vtype_keys,
                ALOOKUP_MEM, check_contract_def] >>
    gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
        get_tenv_def, initial_evaluation_context_def] >>
    drule assignable_type_well_formed >> simp[well_formed_type_def] >>
    strip_tac >> gvs[IS_SOME_EXISTS] >>
    Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
    imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
    gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  Cases_on `base_res` >> simp[] >>
  `0 < type_slot_size x /\ type_slot_size (ArrayTV x b) < dimword(:256)` by
    (`check_toplevel_decl am.layouts tx.target mods art src
        (VariableDecl Public mut fn (ArrayT t b) init)` by
       metis_tac[check_contract_toplevel_decl_MEM] >>
     Cases_on `mut` >>
     gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
         evaluate_type_def, get_tenv_def, initial_evaluation_context_def,
         IS_SOME_EXISTS]) >>
  irule checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix_any_bd >>
  simp[] >>
  qexistsl [`am`,`art`,`b`,`fn`,`init`,`mods`,`mut`,`src`,`st`,`r`,`t`,`ts`,`tx`] >>
  gvs[]
QED

Theorem generated_public_array_getter_aux_premises_from_wrapper[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256))
    (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (base_res,st1) ==>
  ?elem_tv.
    no_type_error_result base_res /\
    (!id aty id' aty'. MEM (id,aty) args /\ MEM (id',aty') args /\
       string_to_num id' = string_to_num id ==> aty' = aty) /\
    pure_expr (TopLevelName NoneT (src,fn)) /\
    evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src))
      (expr_type (TopLevelName NoneT (src,fn))) = SOME NoneTV /\
    evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src))
      (ArrayT_type typ) = SOME elem_tv /\
    (case base_res of
       INL tvl =>
         (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
         (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd)
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `typ` >> gvs[is_ArrayT_def, ArrayT_type_def] >>
  rename1 `ArrayT t b` >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn (ArrayT t b) init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `mut` >>
  gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
      IS_SOME_EXISTS] >>
  Cases_on `evaluate_type (type_env_all_modules mods) t` >>
  gvs[evaluate_type_def] >>
  rename1 `evaluate_type (type_env_all_modules mods) t = SOME elem_tv` >>
  `evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv` by
    simp[get_tenv_def, initial_evaluation_context_def] >>
  qexists `elem_tv` >>
  `no_type_error_result base_res /\
   (case base_res of
      INL tvl =>
        (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd)
    | INR _ => T)` by
    metis_tac[checked_public_array_TopLevelName_base_result_for_generated_getter_aux] >>
  simp[pure_expr_def, expr_type_def, evaluate_type_def,
       get_tenv_def, initial_evaluation_context_def] >>
  metis_tac[generated_public_array_getter_args_num_unique]
QED

Theorem generated_public_array_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr (initial_evaluation_context am.sources am.layouts tx src)
              (TopLevelName NoneT (src,fn)) st` >>
  drule_all generated_public_array_getter_aux_premises_from_wrapper >>
  strip_tac >>
  qspecl_then
    [`ArrayT_type typ`, `TopLevelName NoneT (src,fn)`, `0`, `args`,
     `ret`, `exp`, `get_tenv (initial_evaluation_context am.sources am.layouts tx src)`,
     `vals`, `scope`, `q`, `st`, `r`, `res`, `st'`,
     `initial_evaluation_context am.sources am.layouts tx src`, `elem_tv`, `args`]
    mp_tac generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  simp[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  st.scopes = [scope] /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
    Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) st` >>
    Cases_on `q` >> gvs[]
    >- (`?slot. x = HashMapRef is_transient slot kt vt` by
          (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier_post_prefix]) >>
        gvs[] >>
        `check_value_type (get_tenv cx) vt` by
          (qunabbrev_tac `cx` >>
           `check_value_type (type_env_all_modules mods) vt` by
             metis_tac[checked_hashmap_decl_value_type_checked] >>
           gvs[get_tenv_def, initial_evaluation_context_def]) >>
        irule generated_hashmap_getter_expr_no_type_error_post_prefix >>
        qexistsl [`args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                  `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                  `st`, `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
        simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
        metis_tac[build_getter_args_num_unique]) >>
    `no_type_error_result (INR y)` by
      (qunabbrev_tac `cx` >>
       `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
         (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
          gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
       `find_var_decl_by_num (string_to_num id) ts =
          SOME (HashMapVarDecl is_transient kt vt,id)` by
         metis_tac[find_var_decl_by_num_SOME_hashmap] >>
       `check_toplevel_decl am.layouts tx.target mods art src
          (HashMapDecl Public is_transient id kt vt init)` by
         metis_tac[check_contract_toplevel_decl_MEM] >>
       qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, lookup_global_def, get_module_code_def,
            initial_evaluation_context_def, bind_def, lift_option_type_def,
            return_def, raise_def, lookup_var_slot_from_layout_def,
            lookup_var_slot_in_layouts_def,
            vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
       gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
       rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    qspecl_then [`TopLevelName NoneT (src,id)`, `kt`, `vt`, `0`, `args`,
                 `ret`, `exp`, `cx`, `st`, `y`, `r`, `res`, `st'`]
      mp_tac build_getter_base_error_no_type_error_post_prefix >>
    simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) st` >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier_post_prefix]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_materialisable_shape_post_prefix >>
      qexistsl [`args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st`, `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  qspecl_then [`TopLevelName NoneT (src,id)`, `kt`, `vt`, `0`, `args`,
               `ret`, `exp`, `cx`, `st`, `y`, `r`, `res`, `st'`]
    mp_tac build_getter_base_error_materialisable_shape_post_prefix >>
  simp[]
QED

Theorem selected_public_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule generated_public_array_getter_expr_no_type_error_materialisable_post_prefix >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >>
      drule_all checked_scalar_public_getter_eval_no_type_error_materialisable_post_prefix >> simp[]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule generated_public_hashmap_getter_expr_no_type_error_materialisable_post_prefix >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem checked_public_getter_entry_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
         simp[external_getter_tuple_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx exp (initial_state am [scope])` >>
  irule eval_stmts_single_Return_no_type_error >>
  qexistsl [`cx`, `exp`, `q`, `initial_state am [scope]`, `st'`, `r`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule materialise_getter_result_no_type_error >>
      qexistsl [`cx`, `r`, `st2`, `tv`] >> simp[] >>
      qunabbrev_tac `cx` >>
      drule_all selected_public_getter_expr_no_type_error_materialisable >>
      simp[] >> metis_tac[]) >>
  qunabbrev_tac `cx` >>
  irule (cj 1 selected_public_getter_expr_no_type_error_materialisable) >>
  metis_tac[]
QED

Theorem call_external_function_exact_selected_getter_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `nr = F /\ mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         gvs[external_getter_tuple_def]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
              (initial_state am [scope])` >>
  Cases_on `q` >> gvs[return_def, raise_def]
  >- (`no_type_error_result (FST (eval_stmts
          (initial_evaluation_context am.sources am.layouts tx src) [Return (SOME exp)] r))` by
        (`r = initial_state am [scope]` by
           (qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
            rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
               assert_def, return_def, raise_def] >>
            gvs[AllCaseEqs(), return_def, raise_def]) >>
         gvs[] >>
         Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                    [Return (SOME exp)] (initial_state am [scope])` >>
         drule_all checked_public_getter_entry_no_type_error >>
         simp[]) >>
      Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                  [Return (SOME exp)] r` >>
      Cases_on `q` >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `e`) >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >>
           gvs[initial_evaluation_context_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      rpt strip_tac >> gvs[]) >>
  `no_type_error_eval
     (send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
        (initial_state am [scope]))` by simp[send_call_value_no_type_error_c53] >>
  gvs[initial_evaluation_context_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `y` >> gvs[] >>
  TRY (Cases_on `e`) >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[return_def, raise_def,
           vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem bind_arguments_success_mem_zip_safe_cast[local]:
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

Theorem bind_arguments_success_flookup_safe_cast[local]:
  !tenv params vals scope id ty raw sv.
    bind_arguments tenv params vals = SOME scope /\
    ALL_DISTINCT (MAP (string_to_num o FST) params) /\
    MEM ((id,ty),raw) (ZIP (params, vals)) /\
    FLOOKUP scope (string_to_num id) = SOME sv ==>
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


Theorem lookup_exported_function_checked_cases_current[local]:
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
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
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
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
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


Theorem checked_explicit_external_body_setup[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
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
  drule_all checked_explicit_external_body_typing_package >>
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
      simp[])
QED


Theorem checked_explicit_external_body_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >>
  strip_tac >>
  drule_all eval_stmts_no_type_error >>
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED



Theorem call_external_function_selected_explicit_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts tx.args body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, evaluate_defaults_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def] >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  strip_tac >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  irule checked_explicit_external_entry_no_type_error_selected >>
  qexistsl [`am`, `am'`, `args`, `art`, `body`, `dflts`, `mods`,
            `mut`, `nr`, `raw`, `ret`, `env`, `src`, `ts`, `tx`,
            `tx.args ++ dflt_vs`] >> simp[]
  >- (drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
      gvs[] >>
      qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
      simp[Once call_external_function_def, evaluate_defaults_def,
           initial_evaluation_context_def] >>
      gvs[AllCaseEqs(), initial_evaluation_context_def] >>
      strip_tac >> gvs[]) >>
  metis_tac[]
QED


Theorem call_external_function_selected_getter_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts tx.args body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, evaluate_defaults_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def] >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  strip_tac >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  irule call_external_function_exact_selected_getter_no_type_error_c53 >>
  qexistsl [`am`, `am'`, `args`, `art`, `body`,
            `initial_evaluation_context am.sources am.layouts tx src`,
            `decl`, `dflts`, `mods`, `mut`, `nr`, `ret`, `env`, `src`, `ts`, `tx`,
            `tx.args ++ dflt_vs`] >> simp[]
  >- (drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
      gvs[] >>
      qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
      simp[Once call_external_function_def, evaluate_defaults_def,
           initial_evaluation_context_def] >>
      gvs[AllCaseEqs(), initial_evaluation_context_def] >>
      strip_tac >> gvs[]) >>
  metis_tac[]
QED


(* ===== Checked external call no-TypeError ===== *)

Theorem checked_call_external_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external am tx = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external am tx = (res,am')` mp_tac >>
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
  gvs[]
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_explicit_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `dflts`, `all_mods`, `mut`, `nr`, `raw`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def])
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_getter_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `decl`, `dflts`, `all_mods`, `mut`, `nr`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def])
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_explicit_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `dflts`, `all_mods`, `mut`, `nr`, `raw`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def]) >>
  simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  irule call_external_function_selected_getter_raw_args_no_type_error_c53 >>
  qexistsl [`am`, `am'`, `args`, `art`, `body'`,
            `initial_evaluation_context am.sources am.layouts tx
               (find_function_module am tx.target tx.function_name)`,
            `decl`, `dflts`, `all_mods`, `mut`, `nr`, `ret`,
            `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
  gvs[checked_contract_runtime_ready_def, get_module_code_def,
      initial_evaluation_context_def]
QED





