(* Source and target frames for modelling grouped default initialization. *)
Theory groupedRejectModelFrame
Ancestors
  e2eDefs vyperLoweringCorrect ptrDiscipline fragGasOriginPtr vyperTypeContractContext list
  pred_set venomInst venomState defaultEntrySourcePreparation externalBodyFrame
  entryValueRejectFacts callRejectMemory[ignore_grammar] bodyFullPathHistory
  decoderOriginAllocationFrame venomMemDefs allocaFrontierBound selectedAcceptedFold compileEnv
  vyperContext allocaHistory abiAllocationHistory venomMemProps loweringStateRelDefs
  allocaBudgetProps finite_map rich_list words groupedDefaultSource groupedDefaultState pair
  groupedEntryAllocation arithmetic relation vyperAST

val _ = Parse.hide "tops";

(* Source witnesses for the omitted-default simulation use the selected
   declaration's name and a private, typed empty outcome oracle. *)
Theorem row22_model_initial_rel:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs ==>
  source_typing_ok tops am (tx with function_name := name) /\
  source_deployment_rel tops am (tx with function_name := name) /\
  initial_venom_state_rel tops am (tx with function_name := name)
    (vs with vs_outcomes := [])
Proof
  strip_tac >>
  `source_typing_ok tops am (tx with function_name := name) <=>
   source_typing_ok tops am tx` by
    simp_tac bool_ss [e2eDefsTheory.source_typing_ok_def,
      vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
      vyperContextTheory.call_txn_accfupds] >>
  `source_deployment_rel tops am (tx with function_name := name) <=>
   source_deployment_rel tops am tx` by
    simp_tac bool_ss [source_deployment_rel_def, layouts_agree_def,
      vyperContextTheory.call_txn_accfupds] >>
  `initial_venom_state_rel tops am (tx with function_name := name)
     (vs with vs_outcomes := []) <=> initial_venom_state_rel tops am tx vs` by
    simp_tac bool_ss [initial_venom_state_rel_def, venom_env_rel_def,
      loweringStateRelDefsTheory.call_ctx_rel_def,
      loweringStateRelDefsTheory.tx_env_ok_def, value_transfer_ok_def,
      accounts_after_transfer_def, vyperContextTheory.call_txn_accfupds,
      venom_state_accfupds] >>
  asm_rewrite_tac[]
QED

Theorem row22_model_source:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  set_external_package_target rp.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,ds:expr list,ret,fbody)) =
    (lbl,ce,pos,mc,pay,nr,key,ut,iv,fbody,rt) /\
  (mut = Payable \/ vs.vs_call_ctx.cc_callvalue = 0w) /\
  cx = initial_evaluation_context am.sources am.layouts
    (tx with function_name := name) NONE ==>
  ?art es.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    send_call_value mut cx
      (initial_state am [FEMPTY] with <|outcomes := SOME []; requests := []|>) =
      (INL (),es) /\
    es.scopes = [FEMPTY] /\ es.storage_trace = [] /\
    expr_sim_inv (ce with ce_vars := FEMPTY) cx
      (artifact_env art [(NONE,tops)] NONE) es /\
    body_const_cells_agree [(NONE,tops)] cx (artifact_env art [(NONE,tops)] NONE) es /\
    body_inv tops unit.cu_context (ce with ce_vars := FEMPTY) cx /\
    (ce with ce_vars := FEMPTY).ce_module = NONE /\
    ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
    ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    storage_vars_rel (ce with ce_vars := FEMPTY) cx /\
    transient_vars_rel (ce with ce_vars := FEMPTY) cx /\
    immutable_section_layout (ce with ce_vars := FEMPTY) tops /\
    (!regions : (bool # bytes32 # type_value) list.
       storage_well_formed_on cx (initial_state am []) regions ==>
       storage_well_formed_on cx es regions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all row22_model_initial_rel >> disch_then (qspec_then `name` strip_assume_tac) >>
  qabbrev_tac `tx' = tx with function_name := name` >>
  `tx'.function_name = name /\ tx'.target = tx.target` by simp[Abbr `tx'`] >>
  `source_typing_ok tops am tx' /\ source_deployment_rel tops am tx' /\
   initial_venom_state_rel tops am tx' (vs with vs_outcomes := [])` by
     fs[Abbr `tx'`] >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[e2eDefsTheory.source_typing_ok_def] >>
  `?es. send_call_value mut cx
      (initial_state am [FEMPTY] with <|outcomes := SOME []; requests := []|>) =
      (INL (),es)` by
    (Cases_on `send_call_value mut cx
       (initial_state am [FEMPTY] with <|outcomes := SOME []; requests := []|>)` >>
     Cases_on `q`
     >- (Cases_on `x` >> metis_tac[]) >>
     `mut <> Payable /\ vs.vs_call_ctx.cc_callvalue <> 0w` by
       (mp_tac (Q.INST [`vs` |-> `vs with vs_outcomes := []`, `tx` |-> `tx'`,
                        `env` |-> `FEMPTY`, `mut` |-> `mut`, `e` |-> `y`, `st` |-> `r`]
         (SPEC_ALL entry_value_reject_callvalue)) >>
        qpat_x_assum `cx = _` SUBST_ALL_TAC >> asm_simp_tac (srw_ss()) []) >>
     metis_tac[]) >>
  qexistsl_tac [`art`,`es`] >> asm_rewrite_tac[] >>
  suspend "source_frame"
QED

Resume row22_model_source[source_frame]:
  qpat_x_assum `Abbrev (tx' = _)` kall_tac >>
  qpat_x_assum `tx'.function_name = name` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  `check_contract F am.layouts tx'.target [(NONE,tops)] = SOME art` by simp[] >>
  `outcomes_accounts_typed (SOME [])` by simp[exprSimHypsDefsTheory.outcomes_accounts_typed_def] >>
  `expr_sim_inv (ce with ce_vars := FEMPTY)
    (initial_evaluation_context am.sources am.layouts tx' NONE)
    (artifact_env art [(NONE,tops)] NONE) es` by
    (drule_at (Pat `set_external_package_target _ _ = _`)
       (INST_TYPE [alpha |-> ``:expr``] grouped_default_empty_expr_sim) >>
     disch_then (qspecl_then [`vs with vs_outcomes := []`,`unit`,`es`,
       `initial_evaluation_context am.sources am.layouts tx' NONE`,`art`,`am`] mp_tac) >>
     simp[]) >>
  `(ce with ce_vars := FEMPTY) with ce_vars := ce.ce_vars = ce` by simp[] >>
  drule_at (Pat `set_external_package_target _ _ = _`)
    (INST_TYPE [alpha |-> ``:expr``] external_package_body_inv) >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_all grouped_body_registration_layout >> strip_tac >>
  drule targeted_external_package_layout >> strip_tac >>
  mp_tac (Q.INST [`tx` |-> `tx'`,
      `cx` |-> `initial_evaluation_context am.sources am.layouts tx' NONE`,
      `os` |-> `[]`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] grouped_default_empty_source_frame))) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `env_context_consistent (artifact_env art [(NONE,tops)] NONE)
     (initial_evaluation_context am.sources am.layouts tx' NONE)` by
    (irule check_contract_env_context_consistent_initial_NONE >>
     qexists_tac `tx'.target` >> fs[source_deployment_rel_def]) >>
  `body_const_cells_agree [(NONE,tops)]
     (initial_evaluation_context am.sources am.layouts tx' NONE)
     (artifact_env art [(NONE,tops)] NONE) es` by
    (irule external_source_body_const_cells_checked >>
     simp[vyperTypeContractTheory.artifact_env_def] >>
     qexistsl_tac [`rp`,`unit`] >> first_assum ACCEPT_TAC) >>
  fs[]
QED

Finalise row22_model_source

Theorem row22_model_frame:
  initial_venom_state_rel tops am tx vs /\
  cx.txn = tx /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME []; requests := []|>) = (INL (),es) /\
  selected_registration_frame vs entry_taint u tz /\
  selected_registration_resources ctx fn site 0 sa u /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (vs with <|vs_outcomes := os0; vs_prev_bb := NONE;
      vs_current_bb := "__entry"; vs_inst_idx := 0|>,FEMPTY,entry_taint)
    [] (OK (u with vs_outcomes := os1),J,tz) /\
  ce.ce_modules = [(NONE,tops)] /\ ce.ce_vars = FEMPTY /\ ce.ce_module = NONE /\ ~ce.ce_is_ctor /\
  ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops ==>
  alloca_history fn (u with vs_outcomes := []) /\
  !H:(bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx fn ce cx es (u with vs_outcomes := []) /\
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es J tz (u with vs_outcomes := [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `v = vs with <|vs_outcomes := os0; vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `z = u with vs_outcomes := os1` >>
  qabbrev_tac `w = u with vs_outcomes := []` >>
  `u.vs_initial_fmp = vs.vs_initial_fmp` by
    (drule_all decoder_origin_path_allocation_frame >> simp[Abbr `v`, Abbr `z`]) >>
  `v.vs_allocas = FEMPTY /\ v.vs_inst_idx = 0` by
    fs[Abbr `v`,initial_venom_state_rel_def] >>
  `alloca_history fn v /\ alloca_inv v` by simp[alloca_history_empty, alloca_inv_empty] >>
  `alloca_history fn z /\ abi_alloca_history (fn_insts fn) z` by
    (conj_tac >- metis_tac[body_full_path_alloca_history] >>
     irule grouped_entry_path_abi_history >>
     goal_assum (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
     simp[abi_alloca_history_empty]) >>
  `alloca_history fn w /\ abi_alloca_history (fn_insts fn) w` by
    (conj_tac >-
       (irule alloca_history_frame >> qexists_tac `z` >> simp[Abbr `z`, Abbr `w`]) >>
     irule abi_alloca_history_frame >> qexists_tac `z` >> simp[Abbr `z`, Abbr `w`]) >>
  `(alloca_inv w <=> alloca_inv u) /\
    (alloca_frontier_inv ctx fn site w <=> alloca_frontier_inv ctx fn site u)` by
    (irule calldataDynOwnedTheory.calldata_alloca_invariants_fields >> simp[Abbr `w`]) >>
  `selected_registration_resources ctx fn site 0 sa w` by
    (qpat_assum `selected_registration_resources ctx fn site 0 sa u`
       (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
     PURE_REWRITE_TAC [selected_registration_resources_def] >>
     `alloca_inv w /\ alloca_frontier_inv ctx fn site w` by metis_tac[] >>
     qpat_assum `fresh_vars_wrt sa u`
       (assume_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
     qpat_assum `allocas_from 0 u`
       (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `w`, allocas_from_def, fresh_vars_wrt_def,
       venom_state_accfupds, arithmeticTheory.ZERO_LESS_EQ] >>
     first_assum ACCEPT_TAC) >>
  `default_registration_resources ctx fn site 0 sa w (tz with t_mem := {})` by
    (irule grouped_default_registration_resources >>
     goal_assum (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
     fs[Abbr `w`,selected_registration_frame_def,entry_taint_def,initial_venom_state_rel_def]) >>
  `initial_venom_state_rel tops am tx (vs with vs_outcomes := [])` by
    fs[initial_venom_state_rel_def,venom_env_rel_def] >>
  `selected_registration_frame (vs with vs_outcomes := []) entry_taint w tz` by
    fs[Abbr `w`,selected_registration_frame_def] >>
  `send_call_value mut cx
    (initial_state am [FEMPTY] with
      <|outcomes := SOME (vs with vs_outcomes := []).vs_outcomes; requests := []|>) =
    (INL (),es)` by simp[] >>
  asm_rewrite_tac[] >> gen_tac >>
  drule_all grouped_empty_registration_state >>
  disch_then (qspecl_then [`J`,`cx_dead H cx`] strip_assume_tac) >>
  first_x_assum (qspec_then `H` ACCEPT_TAC)
QED
