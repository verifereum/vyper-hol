(* A selected legacy singleton reaches registration independently of argument representation. *)
Theory groupedLegacyCheckedRoute
Ancestors
  groupedRuntimeBodyCode groupedDispatchPath groupedEntryPackage groupedEntryResources
  groupedEntryExit groupedRegisteredBody groupedEntryAllocation
  runtimeEntryEndpoint registrationRejectMetadata entryRejectAllocationIds
  externalBodyFrame externalReturnPackage defaultEntrySourcePreparation packagedRegistrationProps
  sourceValueRejection selectedAcceptedSingleton selectedAcceptedDecoder
  externalEntryBound gasShadowRuntimeDispatch gasShadowUnit gasShadowState
  vyperCalldata vyperLoweringCorrect e2eDefs compileVyper compileEnv moduleLowering
  ptrDiscipline venomState venomInst list words entryStateRel vyperInterpreter
  sourceUnitExecution gasSummary vyperABI
  groupedLegacyPairedCode groupedLegacyRegistrationMetadata groupedLegacyCheckSeam
  groupedRuntimeEndpoint groupedDefaultArguments
  fragGasOriginPtr venomExecSemantics selectedAcceptedFold constSubst
  gasShadowRuntimeBodies gasShadowModuleDefs gasShadow
  entryValueRejectFacts loweringStateRelDefs vyperState vyperCall finite_map
  groupedValueRejectSite entryCreateGroupedLayout

Theorem grouped_legacy_checked_route_with_reject_site:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
    tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
    (FST (classify_functions tops)) /\
  MAP (package_external_group tops rpolicy.rpol_target T (K global_nonreentrant_slot))
    (FST (classify_functions tops)) =
      pre ++ ExternalSingle (cd_selector vs.vs_call_ctx.cc_calldata,lbl,z) pkg::post /\
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id vs.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults _ es _ _ =>
      FIND (\(sel,_,_,_). calldata_method_id vs.vs_call_ctx.cc_calldata = n2w sel) es = NONE) pre /\
  lbl = "fn_" ++ tx.function_name /\
  pkg = set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,subst_consts_stmts (module_consts_env tops []) fbody)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  bind_arguments (type_env tops) args tx.args = SOME envb /\
  LENGTH tx.args = LENGTH args /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  (!ce0 cf reg sa fn site s u G tn ev.
    send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [FEMPTY] with
        <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),ev) /\
    ALL_DISTINCT (MAP FST args) /\
    (!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ce0 with ce_vars := c.ce_vars ==>
      selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
      abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv) /\
    EVERY (\tv. type_memory_size tv < dimword (:256)) tvs /\
    LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce0.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) args tvs /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
    compile_register_positional_args ce0 (build_positional_args ce0 args) 4 reg = (cf,sa) /\
    fn_has_code reg sa fn /\ fn_inst_ids_distinct fn /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    u.vs_call_ctx = vs.vs_call_ctx /\
    LENGTH u.vs_call_ctx.cc_calldata < dimword (:256) /\
    4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    selected_registration_frame vs entry_taint u tn /\
    selected_registration_resources unit.cu_context fn site 0 reg u /\
    default_registration_resources unit.cu_context fn site 0 reg u (tn with t_mem := {}) /\
    unit_alloca_budget unit.cu_context < dimword (:256) /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
    (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
    local_ptrs_reserved cf sa /\
    cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
    cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
    storage_vars_rel (cf with ce_vars := FEMPTY)
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    transient_vars_rel (cf with ce_vars := FEMPTY)
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    immutable_section_layout (cf with ce_vars := FEMPTY) tops /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (s,FEMPTY,entry_taint) [] (OK u,G,tn)) ==>
    ?es t J tz.
      (!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args [] (es with gas_obs := gx)) /\
      es.gas_obs = [] /\ storage_trace_domain
        (initial_evaluation_context am.sources am.layouts tx NONE) (initial_state am []) es.storage_trace /\
      at_point sa t /\ fresh_vars_wrt sa t /\ return_buf_frame NONE cf sa t /\
      (!H:(bool # bytes32 # type_value) list # num list.
        stmt_state_rel H unit.cu_context fn cf
          (initial_evaluation_context am.sources am.layouts tx NONE) es t /\
        ghost_inv_at (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cf (initial_evaluation_context am.sources am.layouts tx NONE) es J tz t) /\
      !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
        (s,FEMPTY,entry_taint) [] (OK t,J,tz)) ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (grouped_value_reject_site unit vs /\
   ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  qpat_x_assum `MAP _ (FST (classify_functions tops)) = _` (mk_asm "selected") >>
  qpat_x_assum `pkg = set_external_package_target _ _` (mk_asm "package") >>
  qpat_x_assum `lbl = "fn_" ++ tx.function_name` (mk_asm "label") >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> fs[] >>
  drule_all lower_grouped_runtime_pair >>
  disch_then (qx_choosel_then [`groups`,`ips`,`fall`,`shunit`,`fn`,`bb`]
    (map_every assume_tac o CONJUNCTS)) >>
  `shunit = shadow_unit` by fs[] >> gvs[] >>
  drule_all grouped_shadow_entry_dispatch_with_layout >>
  disch_then (qx_choosel_then
    [`shunit`,`shfn`,`sf`,`fall_lbl`,`jobs`,`sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`]
    (map_every assume_tac o CONJUNCTS)) >>
  `shunit = shadow_unit` by fs[] >> gvs[] >>
  asm_x "selected" (assume_tac o REWRITE_RULE [pairTheory.FST]) >>
  asm_x "package" assume_tac >>
  suspend "selector"
QED

Resume grouped_legacy_checked_route_with_reject_site[selector]:
  qabbrev_tac `cd = vs.vs_call_ctx.cc_calldata` >>
  qabbrev_tac `pack = package_external_group tops rpolicy.rpol_target T
    (K global_nonreentrant_slot)` >>
  `MAP pack q = pre ++ ExternalSingle (cd_selector cd,lbl,z) pkg::post` by
    simp[Abbr `pack`,Abbr `cd`] >>
  `EVERY (\group. case group of ExternalSingle _ _ => T
     | ExternalDefaults common entries specs off =>
         EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
     (MAP pack q)` by
    (qunabbrev_tac `pack` >>
     irule (INST_TYPE [alpha |-> ``:160 word``] checked_grouped_package_keyword_widths) >>
     conj_tac >- (qexistsl_tac [`rpolicy`,`unit`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl_tac [`tx.target`,`art`,`am.layouts`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`r2`,`r1`,`r0`] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `ctx_has_dalloca unit.cu_context ==> unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp` by
    metis_tac[] >>
  qpat_assum `Abbrev (s = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all grouped_dispatch_initial_resources >>
  disch_then (qspec_then `ARB` strip_assume_tac) >>
  `s.vs_call_ctx.cc_calldata = cd` by simp[Abbr `s`,Abbr `cd`] >>
  `4 <= LENGTH s.vs_call_ctx.cc_calldata` by simp[] >>
  drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
    (qx_choosel_then [`mid`,`prelude`,`dispatch_end`,`br`,`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  suspend "job"
QED

Resume grouped_legacy_checked_route_with_reject_site[job]:
  `calldata_method_id s.vs_call_ctx.cc_calldata = n2w (cd_selector cd)` by
    (simp[] >> drule calldataSelectorPropsTheory.cd_selector_method_id >> simp[]) >>
  `EVERY (\group. case group of
     ExternalSingle (n,_,_) _ => calldata_method_id cd <> n2w n
   | ExternalDefaults common entries specs _ =>
       FIND (\(n,_,_,_). calldata_method_id cd = n2w n) entries = NONE /\
       EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) pre` by
    (PURE_REWRITE_TAC [EVERY_MEM] >> qx_gen_tac `group` >> strip_tac >>
     `MEM group (MAP pack q)` by
       (qpat_assum `MAP pack q = _` SUBST1_TAC >> simp[MEM_APPEND]) >>
     qpat_assum `EVERY _ (MAP pack q)`
       (mp_tac o Q.SPEC `group` o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `EVERY _ pre`
       (mp_tac o Q.SPEC `group` o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `group` >> simp[pairTheory.ELIM_UNCURRY]) >>
  qpat_assum `MAP pack q = _` (fn eq =>
    qpat_assum `compile_external_groups (Var mid) (MAP pack q) _ = _`
      (assume_tac o REWRITE_RULE [eq]) >>
    qpat_assum `EVERY group_entry_labels_ok (MAP pack q)`
      (assume_tac o REWRITE_RULE [eq])) >>
  `calldata_method_id cd = n2w (cd_selector cd)` by
    (qpat_assum `s.vs_call_ctx.cc_calldata = cd` (SUBST1_TAC o SYM) >>
     qpat_assum `calldata_method_id s.vs_call_ctx.cc_calldata = _` mp_tac >>
     simp[]) >>
  `eval_operand (Var mid) u = SOME (calldata_method_id cd)` by
    (qpat_x_assum `eval_operand (Var mid) u = _` mp_tac >>
     simp[]) >>
  drule_all compile_external_groups_selected_single_origin >>
  disch_then (qspecl_then [`[]`,`Gu`] mp_tac) >>
  strip_tac >>
  rename1 `compile_selector_checks (Var mid) [_] skip_end = ((),sel_end)` >>
  rename1 `selected_registration_frame u tnu hit tnhit` >>
  suspend "installed"
QED

Resume grouped_legacy_checked_route_with_reject_site[installed]:
  PairCases_on `pkg` >>
  drule_all grouped_legacy_paired_code_with_end >>
  disch_then (qx_choosel_then [`checks`,`reg`,`cf`,`sa`,`done`,`sha`,`shdone`] strip_assume_tac) >>
  drule_all_then strip_assume_tac selected_grouped_body_layout_at >>
  `MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
     tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
     (FST (classify_functions tops))` by simp[] >>
  qpat_assum `(pkg0,_,_,_,_,_,_,_,_,_,_) = set_external_package_target _ _`
    (assume_tac o SYM) >>
  drule_all grouped_legacy_registration_metadata >>
  disch_then strip_assume_tac >>
  asm_x "label" assume_tac >>
  `pkg0 = lbl` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [package_external_fn_def,set_external_package_target_def,LET_THM] >>
     simp[]) >>
  qpat_x_assum `pkg0 = lbl` SUBST_ALL_TAC >>
  `EVERY group_entry_labels_ok post` by
    (qpat_assum `EVERY group_entry_labels_ok (pre ++ _)`
       (strip_assume_tac o REWRITE_RULE [EVERY_APPEND,EVERY_DEF]) >>
     first_assum ACCEPT_TAC) >>
  `vs.vs_fmp = vs.vs_initial_fmp` by fs[initial_venom_state_rel_def] >>
  `selected_registration_frame vs entry_taint hit tnhit` by
    (qpat_assum `selected_registration_frame s entry_taint u tnu`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `selected_registration_frame u tnu hit tnhit`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     simp[selected_registration_frame_def,Abbr `s`]) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
     (s,FEMPTY,entry_taint) [] (OK hit,G',tnhit)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  drule_all (REWRITE_RULE [numLib.REDUCE_CONV ``2 ** 254:num``] grouped_legacy_check_seam) >>
  strip_tac >>
  suspend "value"
QED

Resume grouped_legacy_checked_route_with_reject_site[value]:
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by fs[gas_shadow_unit_def] >>
  `MEM fn unit.cu_context.ctx_functions /\ MEM shfn shadow_unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `hit.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame vs entry_taint hit _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [selected_registration_frame_def])) >>
  `vs.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum `initial_venom_state_rel tops am tx vs`
       (strip_assume_tac o REWRITE_RULE [initial_venom_state_rel_def,venom_env_rel_def,call_ctx_rel_def]) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `cx = initial_evaluation_context am.sources am.layouts tx NONE` by simp[Abbr `cx`] >>
  qpat_x_assum `!ce0 cf reg sa fn site s u G tn ev. _` (mk_asm "register") >>
  qabbrev_tac `send = send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>)` >>
  asm_x "register" (fn th =>
    qpat_assum `Abbrev (send = _)`
      (assume_tac o (fn eq => REWRITE_RULE [GSYM eq] th) o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  Cases_on `send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>)` >>
  rename1 `send_call_value _ _ _ = (value_result,ev)` >>
  Cases_on `value_result`
  >- suspend "accept"
  >> suspend "reject"
QED

Resume grouped_legacy_checked_route_with_reject_site[reject]:
  qpat_assum `cx = initial_evaluation_context _ _ _ _` (fn eq =>
    qpat_assum `send_call_value _ cx _ = _` (assume_tac o REWRITE_RULE [eq])) >>
  `value_transfer_ok tx am.accounts` by
    (qpat_assum `initial_venom_state_rel tops am tx vs`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [initial_venom_state_rel_def])) >>
  drule_all send_call_value_rejects_only_nonpayable >> strip_tac >>
  drule_all entry_value_reject_callvalue >> strip_tac >>
  `hit.vs_call_ctx.cc_callvalue <> 0w` by
    (qpat_assum `hit.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `~pkg4` by simp[] >>
  `compile_entry_checks pkg3 F checks = ((),reg)` by
    (qpat_assum `~pkg4` (fn th =>
       qpat_assum `compile_entry_checks pkg3 pkg4 checks = _`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `~block_is_terminated checks` by simp[block_is_terminated_def] >>
  `fresh_vars_wrt checks hit` by
    (qpat_assum `selected_registration_resources _ _ _ _ checks hit`
       (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
     first_assum ACCEPT_TAC) >>
  `hit.vs_current_bb = checks.cs_current_bb` by simp[] >>
  `LENGTH tx.args <= LENGTH args` by simp[] >>
  `LENGTH args - LENGTH tx.args <= 0` by simp[] >>
  qpat_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` (fn eq =>
    qpat_assum `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
       (s,FEMPTY,entry_taint) [] (OK hit,G',tnhit)` (assume_tac o REWRITE_RULE [eq])) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit` by metis_tac[] >>
  disj2_tac >> conj_tac
  >- (irule grouped_value_reject_site_at >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G'`,`bb`,`reg`,`fn`,`pkg3`,`checks`,`hit`,`tnhit`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (REWRITE_RULE [LENGTH] (Q.INST [`defaults` |-> `[]`]
    (SPEC_ALL grouped_entry_value_rejected))) >> strip_tac >>
  qexists_tac `[]` >> simp[gas_explicit_def]
QED

Resume grouped_legacy_checked_route_with_reject_site[accept]:
  `send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),ev)` by
    (qpat_assum `send_call_value _ cx _ = (INL _,_)` mp_tac >> simp_tac (srw_ss()) []) >>
  `cx.txn = tx` by simp[Abbr `cx`,initial_evaluation_context_def] >>
  `pkg4 \/ hit.vs_call_ctx.cc_callvalue = 0w` by
    (drule send_call_value_success_condition >>
     qpat_assum `cx.txn = tx` (fn eq =>
       disch_then (strip_assume_tac o REWRITE_RULE [eq])) >> simp[]) >>
  `hit.vs_call_ctx.cc_calldata = cd` by simp[Abbr `cd`] >>
  `pkg3 <= LENGTH hit.vs_call_ctx.cc_calldata` by
    (simp[] >> decide_tac) >>
  `LENGTH hit.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_assum `hit.vs_call_ctx = _` SUBST1_TAC >>
     drule_all initial_venom_state_calldata_length >> simp_tac bool_ss []) >>
  qpat_assum `(pkg4 \/ hit.vs_call_ctx.cc_callvalue = _) /\ _ ==> _` mp_tac >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qx_choosel_then [`vreg`,`Greg`,`tnreg`] strip_assume_tac) >>
  `vreg.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame vs entry_taint vreg _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [selected_registration_frame_def])) >>
  `LENGTH vreg.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_assum `vreg.vs_call_ctx = _` SUBST1_TAC >>
     drule_all initial_venom_state_calldata_length >> simp_tac bool_ss []) >>
  `!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE` by
    (qx_gen_tac `k` >> Cases_on `FLOOKUP cf.ce_vars k` >> simp[] >> metis_tac[]) >>
  `compile_register_positional_args pkg1 (build_positional_args pkg1 args) 4 reg = (cf,sa)` by
    metis_tac[] >>
  `SUM (MAP tv_abi_size tvs) + 4 < dimword (:256)` by
    (qpat_assum `pkg3 < dimword (:256)` mp_tac >> asm_rewrite_tac[] >> decide_tac) >>
  `send = (INL (),ev)` by simp[Abbr `send`] >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `!ce0 cf reg sa fn site s u G tn ev. _ ==> ?es t J tz. _` (fn cont =>
    drule_all cont) >>
  disch_then (qx_choosel_then [`es`,`t`,`J`,`tz`] strip_assume_tac) >>
  disj1_tac >> qexists_tac `es` >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`pkg5 = nr`, `pkg6 = global_nonreentrant_slot`, `pkg8 = (mut = View)`,
     `pkg9 = subst_consts_stmts _ _`, `pkg10 = _`] >>
  qpat_x_assum `pkg7` (SUBST_ALL_TAC o EQT_INTRO) >>
  `nr ==> fresh_vars_wrt sa t` by simp[] >>
  `!D. gas_origin_ptr_path
      (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,fn,[])
      (s,FEMPTY,entry_taint) [] (OK t,J,tz)` by
    (gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  irule (REWRITE_RULE [gas_explicit_nil, APPEND, MAP,
      constSubstCorrectTheory.subst_consts_exprs_map]
    (Q.INST [`marks` |-> `[]`, `dflts` |-> `[]`,
      `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
      `body` |-> `subst_consts_stmts (module_consts_env tops []) fbody`]
      (SPEC_ALL grouped_registered_body_endpoint))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `fbody` >> simp[] >> NO_TAC) >>
  qexistsl_tac [`J`,`bb`,`cf`,`pkg1`,`done`,`fn`,`pkg4`,`mut = View`,`lbl`,
    `pkg3`,`global_nonreentrant_slot`,`pkg2`,`if ret = NoneT then NONE else SOME ret`,
    `s`,`sa`,`shdone`,`shfn`,`sha`,`shadow_unit`,`t`,`tz`,`T`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise grouped_legacy_checked_route_with_reject_site

Theorem grouped_legacy_checked_route:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
    tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
    (FST (classify_functions tops)) /\
  MAP (package_external_group tops rpolicy.rpol_target T (K global_nonreentrant_slot))
    (FST (classify_functions tops)) =
      pre ++ ExternalSingle (cd_selector vs.vs_call_ctx.cc_calldata,lbl,z) pkg::post /\
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id vs.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults _ es _ _ =>
      FIND (\(sel,_,_,_). calldata_method_id vs.vs_call_ctx.cc_calldata = n2w sel) es = NONE) pre /\
  lbl = "fn_" ++ tx.function_name /\
  pkg = set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,subst_consts_stmts (module_consts_env tops []) fbody)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  bind_arguments (type_env tops) args tx.args = SOME envb /\
  LENGTH tx.args = LENGTH args /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH vs.vs_call_ctx.cc_calldata /\
  (!ce0 cf reg sa fn site s u G tn ev.
    send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [FEMPTY] with
        <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),ev) /\
    ALL_DISTINCT (MAP FST args) /\
    (!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ce0 with ce_vars := c.ce_vars ==>
      selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
      abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv) /\
    EVERY (\tv. type_memory_size tv < dimword (:256)) tvs /\
    LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce0.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) args tvs /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
    compile_register_positional_args ce0 (build_positional_args ce0 args) 4 reg = (cf,sa) /\
    fn_has_code reg sa fn /\ fn_inst_ids_distinct fn /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    u.vs_call_ctx = vs.vs_call_ctx /\
    LENGTH u.vs_call_ctx.cc_calldata < dimword (:256) /\
    4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    selected_registration_frame vs entry_taint u tn /\
    selected_registration_resources unit.cu_context fn site 0 reg u /\
    default_registration_resources unit.cu_context fn site 0 reg u (tn with t_mem := {}) /\
    unit_alloca_budget unit.cu_context < dimword (:256) /\
    (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
    (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
    local_ptrs_reserved cf sa /\
    cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
    cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
    storage_vars_rel (cf with ce_vars := FEMPTY)
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    transient_vars_rel (cf with ce_vars := FEMPTY)
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    immutable_section_layout (cf with ce_vars := FEMPTY) tops /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (s,FEMPTY,entry_taint) [] (OK u,G,tn)) ==>
    ?es t J tz.
      (!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args [] (es with gas_obs := gx)) /\
      es.gas_obs = [] /\ storage_trace_domain
        (initial_evaluation_context am.sources am.layouts tx NONE) (initial_state am []) es.storage_trace /\
      at_point sa t /\ fresh_vars_wrt sa t /\ return_buf_frame NONE cf sa t /\
      (!H:(bool # bytes32 # type_value) list # num list.
        stmt_state_rel H unit.cu_context fn cf
          (initial_evaluation_context am.sources am.layouts tx NONE) es t /\
        ghost_inv_at (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cf (initial_evaluation_context am.sources am.layouts tx NONE) es J tz t) /\
      !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
        (s,FEMPTY,entry_taint) [] (OK t,J,tz)) ==>
  (?es. runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args [] ret
    (subst_consts_stmts (module_consts_env tops []) fbody)) \/
  (?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))))
Proof
  disch_then (mp_tac o MATCH_MP grouped_legacy_checked_route_with_reject_site) >>
  strip_tac >> metis_tac[]
QED
