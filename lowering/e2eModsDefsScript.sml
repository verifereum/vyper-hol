(* Runtime boundary and gas exemptions for linked units. *)
Theory e2eModsDefs
Ancestors
  e2eDefs e2eCorrectness[qualified] e2eGasSufficient[qualified]
  bodyInvSplit bodySimModsProps[qualified] bodySim[qualified]
  compileUnit compileVyper compileEnv immutableSectionRel immutableRelation
  immutableLocationProps immSectionDead
  immutableValue immutableEncoding valueEncoding valueEncodingDefs loweringStateRelDefs
  vyperInterpreter vyperContext vyperState vyperTypeContract vyperTypeInvariants
  vyperTypeCallGraphSoundness vyperTypeContractContext
  vyperABI vyperABIEntries vyperCalldata supportedStmtTraverse
  sourceExemptMods vyperStorageFootprint callTrace frameOutcome frameGas vfmExecution vfmState
  alist finite_map list pair

(* Linked bytecode uses annotated offsets, so its allocated immutables
   must partition the section. The singleton allocator puts them in order. *)
Theorem singleton_immutable_regions_partition[local]:
  (!src name off size.
     immutable_region_mods [(NONE, tops)] src name off size ==>
     off + size <= imm_len_mods [(NONE, tops)]) /\
  (!src name off size src' name' off' size'.
     (src,name) <> (src',name') /\
     immutable_region_mods [(NONE, tops)] src name off size /\
     immutable_region_mods [(NONE, tops)] src' name' off' size' ==>
     loweringStateRelDefs$regions_disjoint off size off' size') /\
  (!i. i < imm_len_mods [(NONE, tops)] ==>
     ?src name off size.
       immutable_region_mods [(NONE, tops)] src name off size /\
       off <= i /\ i < off + size)
Proof
  rpt conj_tac
  >- (simp[bodySimModsPropsTheory.singleton_immutable_region,
           imm_len_mods_singleton, imm_len_def] >>
      rpt strip_tac >> gvs[compute_immutables_len_append, compute_immutables_len_def])
  >- (simp[bodySimModsPropsTheory.singleton_immutable_region] >>
      rpt strip_tac >> gvs[] >>
      rename1 `left_name <> right_name` >>
      rename1 `_ ++ [VariableDecl right_vis Immutable right_name _ right_slot] ++ right_post =
               _ ++ [VariableDecl left_vis Immutable left_name _ left_slot] ++ left_post` >>
      irule immutable_layout_disjoint >>
      qexistsl [`left_name`, `right_name`, `left_post`, `right_post`,
                `left_slot`, `right_slot`, `left_vis`, `right_vis`] >>
      simp[] >> metis_tac[]) >>
  simp[imm_len_mods_singleton, imm_len_def, bodySimModsPropsTheory.singleton_immutable_region] >>
  gen_tac >> strip_tac >> drule bodySimTheory.compute_immutables_len_byte_coverage >> strip_tac >>
  qexistsl [`name`,
            `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre`,
            `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty`] >>
  simp[] >> qexistsl [`pre`, `post`, `vis`, `ty`, `slot`] >> simp[]
QED

Definition linked_state_ownership_ok_def:
  linked_state_ownership_ok layouts addr mods exps <=>
    check_linked_state_ownership layouts addr mods (linked_live_functions mods exps)
End

Theorem linked_state_ownership_ok_singleton[simp]:
  linked_state_ownership_ok layouts addr [(NONE, tops)] []
Proof
  simp[linked_state_ownership_ok_def, check_linked_state_ownership_def]
QED

Theorem check_contract_linked_state_ownership_ok:
  check_contract in_deploy layouts addr mods = SOME art /\
  exports_ok layouts addr mods exps ==>
  linked_state_ownership_ok layouts addr mods exps
Proof
  strip_tac >>
  `check_linked_state_ownership layouts addr mods
     (linked_live_functions_from mods (linked_main_roots mods))` by
    fs[check_contract_def] >>
  `check_linked_state_ownership layouts addr mods
     (linked_live_functions_from mods (linked_export_roots exps))` by
    fs[exports_ok_def] >>
  Cases_on `(case mods of [(NONE,_)] => T | _ => F)` >>
  gvs[linked_state_ownership_ok_def, check_linked_state_ownership_def,
      EVERY_MEM, FORALL_PROD] >>
  qx_genl_tac [`src`, `tops`] >> strip_tac >>
  qx_gen_tac `tl` >> strip_tac >>
  ntac 2 (qpat_x_assum `!s ts. MEM (s,ts) mods ==> _`
    (qspecl_then [`src`, `tops`]
      (fn th => mp_tac (th |> UNDISCH |> Q.SPEC `tl` |> UNDISCH)))) >>
  Cases_on `tl` >> simp[linked_live_functions_member, DISJ_IMP_THM] >>
  rpt CASE_TAC >> simp[DISJ_IMP_THM]
QED

Theorem check_contract_linked_lock_slot:
  check_contract in_deploy layouts addr mods = SOME art /\
  exports_ok layouts addr mods exps /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
  ALOOKUP (case ALOOKUP layouts addr of NONE => [] | SOME (_,tl) => tl)
    (NONE,"$.nonreentrant_key") = SOME global_nonreentrant_slot
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by fs[check_contract_def, contract_namespaces_ok_def] >>
  `ALOOKUP mods src = SOME tops` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  `vis <> Deploy` by metis_tac[check_contract_deploy_nonreentrant] >>
  `function_live layouts addr mods (live_functions layouts addr mods) (src,name)` by
    metis_tac[check_contract_main_module_allocated, module_allocated_function_live,
              linked_live_functions_function_live] >>
  `check_function_body layouts addr mods art src vis mut T args dflts ret stmts` by
    metis_tac[check_contract_function_body_MEM, check_function_body_in_mode_def] >>
  fs[check_function_body_def, contextTheory.global_nonreentrant_slot_def] >>
  Cases_on `ALOOKUP layouts addr` >> gvs[lookup_nonreentrant_slot_def] >>
  PairCases_on `x` >> gvs[]
QED

(* Storage and transient declarations use their module-qualified keys.
   The lock has one reserved slot for the entire contract. *)
Definition layouts_agree_mods_def:
  layouts_agree_mods mods exps am tx <=>
    (!src name off size.
       immutable_region_mods mods src name off size ==>
       off + size <= imm_len_mods mods) /\
    (!src name off size src' name' off' size'.
       (src,name) <> (src',name') /\
       immutable_region_mods mods src name off size /\
       immutable_region_mods mods src' name' off' size' ==>
       loweringStateRelDefs$regions_disjoint off size off' size') /\
    (!i. i < imm_len_mods mods ==>
       ?src name off size.
         immutable_region_mods mods src name off size /\
         off <= i /\ i < off + size) /\
    let (sl, tl) = (case ALOOKUP am.layouts tx.target of
                      SOME p => p | NONE => ([], [])) in
    !src tops. MEM (src, tops) mods ==>
      (!vis id ty slot_opt. MEM (VariableDecl vis Storage id ty slot_opt) tops ==>
                            ALOOKUP sl (src, id) = slot_opt) /\
      (!vis id ty slot_opt. MEM (VariableDecl vis Transient id ty slot_opt) tops ==>
                            ALOOKUP tl (src, id) = slot_opt) /\
      (!vis tr id kt vt slot_opt. MEM (HashMapDecl vis tr id kt vt slot_opt) tops ==>
                                  ALOOKUP (if tr then tl else sl) (src, id) = slot_opt) /\
      (!vis mut rr name args dflts ret body.
         MEM (FunctionDecl vis mut T rr name args dflts ret body) tops /\
         (src = NONE \/ MEM (src, name) (linked_live_functions mods exps)) ==>
         ALOOKUP tl (NONE, "$.nonreentrant_key") =
           SOME global_nonreentrant_slot)
End

Theorem layouts_agree_mods_singleton:
  layouts_agree_mods [(NONE, tops)] [] am tx <=> layouts_agree tops am tx
Proof
  mp_tac singleton_immutable_regions_partition >>
  simp[layouts_agree_mods_def, layouts_agree_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

(* The interpreter treats a missing export entry as an empty list. *)
Definition source_deployment_rel_mods_def:
  source_deployment_rel_mods mods exps am tx <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    ALOOKUP mods NONE <> NONE /\
    (ALOOKUP am.exports tx.target = SOME exps \/
     exps = [] /\ ALOOKUP am.exports tx.target = NONE) /\
    layouts_agree_mods mods exps am tx
End

Theorem source_deployment_rel_mods_singleton:
  source_deployment_rel_mods [(NONE, tops)] [] am tx <=>
    source_deployment_rel tops am tx
Proof
  simp[source_deployment_rel_mods_def, source_deployment_rel_def,
       layouts_agree_mods_singleton, DISJ_COMM]
QED

Definition global_cells_typed_mods_def:
  global_cells_typed_mods mods globals imms <=>
    !src id ty.
      FLOOKUP globals (src, id) = SOME ty ==>
      ?tv v.
        FLOOKUP (get_source_immutables src imms) id = SOME (tv, v) /\
        evaluate_type (type_env_all_modules mods) ty = SOME tv
End

Theorem global_cells_typed_mods_singleton:
  global_cells_typed_mods [(NONE, tops)] globals imms <=>
    global_cells_typed tops globals imms
Proof
  simp[global_cells_typed_mods_def, global_cells_typed_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

(* Each module's folded constant cells must already be present at call entry. *)
Definition source_typing_ok_mods_def:
  source_typing_ok_mods mods exps am tx <=>
    ?art.
      check_contract F am.layouts tx.target mods = SOME art /\
      exports_ok am.layouts tx.target mods exps /\
      global_cells_typed_mods mods art.cta_bare_globals (account_immutables am tx.target) /\
      (!src tops. MEM (src, tops) mods ==>
        ?cenv.
          constants_fold_module mods (account_immutables am tx.target)
            src tops FEMPTY = SOME cenv /\
          cenv SUBMAP get_source_immutables src (account_immutables am tx.target)) /\
      machine_well_typed am /\ call_tx_well_typed tx
End

Theorem source_typing_ok_mods_singleton:
  source_typing_ok_mods [(NONE, tops)] [] am tx <=> source_typing_ok tops am tx
Proof
  simp[source_typing_ok_mods_def, source_typing_ok_def,
       global_cells_typed_mods_singleton] >>
  metis_tac[check_contract_single_module_exports_ok]
QED

(* The linked allocator supplies the offset and width of each allocated
   immutable, including those in initialized imports. *)
Definition immutables_section_rel_mods_def:
  immutables_section_rel_mods mods imms (section:word8 list) <=>
    LENGTH section = imm_len_mods mods /\
    !src name off size. immutable_region_mods mods src name off size ==>
      ?tv v. FLOOKUP (get_source_immutables src imms) name = SOME (tv,v) /\
        immutable_value_admissible tv v /\
        type_memory_size tv = size /\
        val_in_memory tv v off section /\
        immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) section)
End

Theorem immutables_section_rel_mods_singleton:
  immutables_section_rel_mods [(NONE, tops)] imms section <=>
    immutables_section_rel tops imms section
Proof
  simp[immutables_section_rel_mods_def, immutables_section_rel_def,
       imm_len_mods_singleton, immSectionDeadTheory.imm_len_def,
       immutable_region_mods_def, make_struct_fields_map_mods_singleton] >>
  metis_tac[]
QED

Definition installed_code_rel_mods_def:
  installed_code_rel_mods mods runtime imms code <=>
    ?section. code = runtime ++ section /\
      immutables_section_rel_mods mods imms section
End

Theorem installed_code_rel_mods_singleton:
  installed_code_rel_mods [(NONE, tops)] runtime imms code <=>
    installed_code_rel tops runtime imms code
Proof
  simp[installed_code_rel_mods_def, installed_code_rel_def,
       immutables_section_rel_mods_singleton]
QED

Definition call_state_rel_mods_def:
  call_state_rel_mods mods exps runtime_bc am tx es <=>
    ?ctxt rb rest.
      es.contexts = (ctxt, rb) :: rest /\
      evm_state_ok es /\ (?d. es.msdomain = Collect d) /\
      frame_fresh ctxt /\ (?mr. ctxt.msgParams.outputTo = Memory mr) /\
      frame_tx_rel tx es ctxt /\
      world_rel am tx es /\
      installed_code_rel_mods mods runtime_bc (account_immutables am tx.target)
        ctxt.msgParams.code /\
      (lookup_account tx.target es.rollback.accounts).code =
        ctxt.msgParams.code /\
      source_deployment_rel_mods mods exps am tx
End

Theorem call_state_rel_mods_singleton:
  call_state_rel_mods [(NONE, tops)] [] runtime_bc am tx es <=>
    call_state_rel tops runtime_bc am tx es
Proof
  simp[call_state_rel_mods_def, call_state_rel_def,
       installed_code_rel_mods_singleton, source_deployment_rel_mods_singleton]
QED

(* Decode the linked unit's deployed interface, with the same bounded
   decoder and pre-body miss/rejection behaviour as the singleton. *)
Definition calldata_dispatch_mods_def:
  calldata_dispatch_mods mods exps cd =
    let tenv = type_env_all_modules mods in
    let hit = if LENGTH cd < 4 then NONE
              else FIND (\(name,tys). abi_method_id tenv name tys = cd_selector cd)
                        (abi_deployed_signatures mods exps) in
    case hit of
      NONE =>
        if EXISTS is_default_decl (main_module mods) \/
           IS_SOME (exported_fallback mods exps)
        then SOME ("__default__", [])
        else NONE
    | SOME (name, tys) =>
      case OPT_MMAP (evaluate_type tenv) tys of
        NONE => NONE
      | SOME tvs =>
        if LENGTH cd < 4 + SUM (MAP tv_abi_size tvs) then NONE
        else case calldata_decode_args cd tvs 0 of
               NONE => NONE
             | SOME vs => SOME (name, vs)
End

Theorem calldata_dispatch_mods_singleton:
  calldata_dispatch_mods [(NONE, tops)] [] cd = calldata_dispatch tops cd
Proof
  simp[calldata_dispatch_mods_def, calldata_dispatch_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2,
       abi_deployed_signatures_def, main_module_def, exported_fallback_def]
QED

Definition return_bytes_mods_def:
  return_bytes_mods mods ret v out <=>
    let tenv = type_env_all_modules mods in
    if ret = NoneT then out = []
    else ?abi_v.
           vyper_to_abi tenv ret v = SOME abi_v /\
           out = if needs_external_call_wrap ret
                 then enc (Tuple [vyper_to_abi_type tenv ret]) (ListV [abi_v])
                 else enc (vyper_to_abi_type tenv ret) abi_v
End

Theorem return_bytes_mods_singleton:
  return_bytes_mods [(NONE, tops)] ret v out <=> return_bytes tops ret v out
Proof
  simp[return_bytes_mods_def, return_bytes_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

(* Resolve return metadata in the same module call_external selects. *)
Definition external_return_type_mods_def:
  external_return_type_mods mods exps f =
    let src = ALOOKUP exps f in
    case ALOOKUP mods src of
      NONE => NoneT
    | SOME tops =>
        case vyperInterpreter$lookup_function src f External tops of
          SOME (_, _, _, _, ret, _) => ret
        | NONE => NoneT
End

Theorem external_return_type_mods_singleton:
  external_return_type_mods [(NONE, tops)] [] f = external_return_type tops f
Proof
  simp[external_return_type_mods_def, external_return_type_def]
QED

Definition tx_return_bytes_mods_def:
  tx_return_bytes_mods mods exps tx v out <=>
    let src = ALOOKUP exps tx.function_name in
    let raw = case ALOOKUP mods src of
                NONE => F
              | SOME tops =>
                  lookup_raw_return_or_F src tx.function_name External tops in
    if raw then raw_return_bytes v = SOME out
    else return_bytes_mods mods (external_return_type_mods mods exps tx.function_name) v out
End

Theorem tx_return_bytes_mods_singleton:
  tx_return_bytes_mods [(NONE, tops)] [] tx v out <=> tx_return_bytes tops tx v out
Proof
  simp[tx_return_bytes_mods_def, tx_return_bytes_def, external_return_type_mods_singleton,
       return_bytes_mods_singleton]
QED

Definition source_exempt_mods_def:
  source_exempt_mods mods (src : (value + exception) # abstract_machine # call_request list) <=>
    case FST src of INR (Error e) => unspecified_behaviour_exempt_mods mods e | _ => F
End

Theorem source_exempt_mods_singleton:
  source_exempt_mods [(NONE, tops)] src <=> source_exempt tops src
Proof
  simp[source_exempt_mods_def, source_exempt_def,
       unspecified_behaviour_exempt_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Definition gas_source_exempt_mods_def:
  gas_source_exempt_mods mods tx
    (src : (value + exception) # abstract_machine # call_request list) <=>
    source_exempt_mods mods src \/
    FST src = INR (Error (RuntimeError "create initcode too large")) \/
    (tx.is_static /\
     ((?m. m <> "msg.gas: no gas reading" /\
           FST src = INR (Error (RuntimeError m))) \/
      FST src = INR (AssertException "UNREACHABLE")))
End

Theorem gas_source_exempt_mods_singleton:
  gas_source_exempt_mods [(NONE, tops)] tx src <=> e2eGasSufficient$gas_source_exempt tops tx src
Proof
  simp[gas_source_exempt_mods_def, e2eGasSufficientTheory.gas_source_exempt_def,
       source_exempt_mods_singleton]
QED

Definition exception_outcome_rel_mods_def:
  exception_outcome_rel_mods mods exc es r es' <=>
    case exc of
      AssertException s =>
        ?failure out lgs.
          frame_outcome es r es' (SOME failure) out lgs /\
          ((failure = Reverted /\ frame_raises es Reverted) \/ s = "UNREACHABLE")
    | Error e =>
        unspecified_behaviour_exempt_mods mods e \/
        ?failure out lgs.
          frame_outcome es r es' (SOME failure) out lgs /\
          (!d. e = RevertData d ==> failure = Reverted /\ frame_raises es Reverted)
    | _ => F
End

Theorem exception_outcome_rel_mods_singleton:
  exception_outcome_rel_mods [(NONE, tops)] exc es r es' <=>
    exception_outcome_rel tops exc es r es'
Proof
  simp[exception_outcome_rel_mods_def, exception_outcome_rel_cases,
       unspecified_behaviour_exempt_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Definition call_result_rel_at_mods_def:
  call_result_rel_at_mods gobs mods exps am tx es r es' <=>
    let os = MAP SND (call_trace es) in
    let touched = storage_trace_horizon (source_storage_trace am tx os gobs) in
    let (res, am', rqs) = call_external (SOME os) gobs am tx in
    case res of
      INL v => ?out. tx_return_bytes_mods mods exps tx v out /\
                     frame_outcome es r es' NONE out am'.logs /\
                     effects_agree touched tx (am', rqs) es es'
    | INR HaltException => frame_outcome es r es' NONE [] am'.logs /\
                           effects_agree touched tx (am', rqs) es es'
    | INR exc => exception_outcome_rel_mods mods exc es r es'
End

Theorem call_result_rel_at_mods_singleton:
  call_result_rel_at_mods gobs [(NONE, tops)] [] am tx es r es' <=>
    call_result_rel_at gobs tops am tx es r es'
Proof
  simp[call_result_rel_at_mods_def, call_result_rel_at_def] >>
  pairarg_tac >>
  simp[tx_return_bytes_mods_singleton, exception_outcome_rel_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Definition call_result_rel_mods_def:
  call_result_rel_mods H mods exps am tx es r es' <=>
    let os = MAP SND (call_trace es) in
    gas_readings_rel (gas_readings es)
      (\gobs. call_result_rel_at_mods gobs mods exps am tx es r es' /\
              let (res, am', rqs) = call_external (SOME os) gobs am tx in
                e2eCorrectness$storage_ok H am' tx)
End

Theorem call_result_rel_mods_singleton:
  call_result_rel_mods H [(NONE, tops)] [] am tx es r es' <=>
    e2eCorrectness$call_result_rel H tops am tx es r es'
Proof
  simp[call_result_rel_mods_def, e2eCorrectnessTheory.call_result_rel_def,
       call_result_rel_at_mods_singleton]
QED

Definition call_within_mods_def:
  call_within_mods H mods exps am tx es <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
    !f vals gobs.
      calldata_dispatch_mods mods exps tx.calldata = SOME (f, vals) ==>
      storage_observations_ok cx H
        (source_storage_trace am (tx with <| function_name := f; args := vals |>)
           (MAP SND (call_trace es)) gobs)
End

Theorem call_within_mods_singleton:
  call_within_mods H [(NONE, tops)] [] am tx es <=>
    e2eCorrectness$call_within H tops am tx es
Proof
  simp[call_within_mods_def, e2eCorrectnessTheory.call_within_def,
       calldata_dispatch_mods_singleton]
QED

Definition calldata_result_rel_mods_def:
  calldata_result_rel_mods H mods exps am tx es r es' <=>
    case calldata_dispatch_mods mods exps tx.calldata of
      NONE => frame_raises es Reverted /\
              ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs
    | SOME (f, vals) =>
        call_result_rel_mods H mods exps am
          (tx with <| function_name := f; args := vals |>) es r es'
End

Theorem calldata_result_rel_mods_singleton:
  calldata_result_rel_mods H [(NONE, tops)] [] am tx es r es' <=>
    e2eCorrectness$calldata_result_rel H tops am tx es r es'
Proof
  simp[calldata_result_rel_mods_def, e2eCorrectnessTheory.calldata_result_rel_def,
       calldata_dispatch_mods_singleton, call_result_rel_mods_singleton] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED
