Theory concretizePtrDallocaRuntimeControl
Ancestors
  concretizePtrDallocaRuntimeCall concretizePtrDallocaRuntimeRet
  concretizePtrDallocaGhostInterface callLayoutDefs
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrPairedCallEntry o1FrameLockstep
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrHistoricalWriteExclusion
  concretizePtrOperationalOpcodes concretizePtrStagePairedBridge
  concretizeStepStructure concretizeStepShape o1PassLift o1PassContract
  venomWf unitShapeDefs
  venomExecSemantics venomState venomInst ptrDiscipline
  finite_map pred_set list rich_list arithmetic

(* The pushed caller records are exposed so the actual history can extend
   its saved relation directly, without imposing a parameter-vector length. *)
Theorem ptr_dalloca_runtime_chrono_call:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  ptr_chrono_step Ct at bt /\
  a.po_inst.inst_opcode = INVOKE /\ at.po_inst = a.po_inst /\
  (!name fn. lookup_function name C.ctx_functions = SOME fn ==>
     first_block_no_phi fn) /\
  (!name fn. lookup_function name Ct.ctx_functions = SOME fn ==>
     first_block_no_phi fn) /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
     FLOOKUP at.po_prov v = SOME site) ==>
  ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TG' v = NONE) /\
  (!v site. FLOOKUP TG' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site) /\
  LENGTH PT' = LENGTH b.po_params /\
  LENGTH b.po_params = LENGTH bt.po_params /\
  (!k site. k < LENGTH b.po_params ==>
    (EL k bt.po_params = SOME site ==>
      EL k b.po_params = SOME site /\ EL k PT' = NONE /\
      EL k b.po_state.vs_params = EL k bt.po_state.vs_params) /\
    (EL k PT' = NONE /\ EL k b.po_params = SOME site ==>
      EL k bt.po_params = SOME site)) /\
  saved' = (PT,TG)::saved /\
  b.po_stack =
    <| cf_fn := a.po_fn; cf_inst := a.po_inst; cf_state := a.po_state;
       cf_params := a.po_params; cf_prov := a.po_prov;
       cf_tvar := a.po_taint.t_var |> :: a.po_stack /\
  bt.po_stack =
    <| cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var |> :: at.po_stack
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def,
       ptr_observation_component_equality, is_terminator_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    metis_tac[step_inst_invoke_not_intret]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def,
       ptr_observation_component_equality, is_terminator_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    metis_tac[step_inst_invoke_not_intret]) >>
  `first_block_no_phi b.po_fn /\ first_block_no_phi bt.po_fn` by metis_tac[] >>
  imp_res_tac ptr_setup_no_phi_entry >> gvs[] >>
  drule_all ptr_dalloca_runtime_call >> strip_tac >>
  simp[ptr_dalloca_ghost_vars_def, op_taint_def, entry_taint_def]
QED

(* Pop only the actual saved heads. Their parameter values survive output
   binding, independently of how many values the active callee returns. *)
Theorem ptr_dalloca_runtime_chrono_ret:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  ptr_chrono_step Ct at bt /\
  a.po_stack = f::stk /\ at.po_stack = ft::stkt /\
  saved = (RPT,RTG)::tail /\
  is_raw_return_opcode a.po_inst.inst_opcode /\ at.po_inst = a.po_inst /\
  ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
    ft.cf_prov ft.cf_tvar ft.cf_state /\
  (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP RTG v = NONE) /\
  (!v site. FLOOKUP RTG v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
     FLOOKUP ft.cf_prov v = SOME site) /\
  f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
  LENGTH RPT = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
  (!k site. k < LENGTH f.cf_params ==>
    (EL k ft.cf_params = SOME site ==>
      EL k f.cf_params = SOME site /\ EL k RPT = NONE /\
      EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
    (EL k RPT = NONE /\ EL k f.cf_params = SOME site ==>
      EL k ft.cf_params = SOME site)) ==>
  ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TG' v = NONE) /\
  (!v site. FLOOKUP TG' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site) /\
  PT' = RPT /\ saved' = tail /\
  b.po_stack = stk /\ bt.po_stack = stkt /\
  LENGTH PT' = LENGTH b.po_params /\
  LENGTH b.po_params = LENGTH bt.po_params /\
  (!k site. k < LENGTH b.po_params ==>
    (EL k bt.po_params = SOME site ==>
      EL k b.po_params = SOME site /\ EL k PT' = NONE /\
      EL k b.po_state.vs_params = EL k bt.po_state.vs_params) /\
    (EL k PT' = NONE /\ EL k b.po_params = SOME site ==>
      EL k bt.po_params = SOME site))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def,
       ptr_observation_component_equality] >> strip_tac >>
  gvs[ptr_observation_component_equality, is_raw_return_opcode_def,
      is_terminator_def]
  >>~- ([`step_inst _ _ _ _ = OK _`],
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
    rpt strip_tac >> pairarg_tac >> gvs[]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def,
       ptr_observation_component_equality] >> strip_tac >>
  gvs[ptr_observation_component_equality, is_terminator_def]
  >>~- ([`step_inst _ _ _ _ = OK _`],
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
    rpt strip_tac >> pairarg_tac >> gvs[]) >>
  imp_res_tac ptr_dalloca_return_params >>
  rename1 `bind_outputs _ ret_src_witness.iret_values
    (adopt_return_fmp ret_src_witness (merge_callee_state f.cf_state end_src_state)) =
    SOME raw_src_after` >>
  rename1 `bind_outputs _ ret_tgt_witness.iret_values
    (adopt_return_fmp ret_tgt_witness (merge_callee_state ft.cf_state end_tgt_state)) =
    SOME raw_tgt_after` >>
  mp_tac (Q.INST [
    `f` |-> `f`, `ft` |-> `ft`, `TG` |-> `RTG`,
    `ret` |-> `ret_src_witness`, `rett` |-> `ret_tgt_witness`,
    `e` |-> `end_src_state`, `et` |-> `end_tgt_state`,
    `s1` |-> `raw_src_after`, `t1` |-> `raw_tgt_after`]
    (INST_TYPE [alpha |-> ``:num # num``] ptr_dalloca_runtime_ret)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs`
    (fn th => fs[th])
QED

(* Matching departed instruction IDs selects the actual rewritten cursor,
   including observations before a normalized target sample. *)
Theorem ptr_dalloca_historical_control_inst[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht endpoint_t done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n = EL q done /\
  a = EL n h /\ at = EL q ht /\
  a.po_inst.inst_opcode <> ALLOCA ==> at.po_inst = a.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht /\ n < LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_observation_reachable vs C a` by
    (drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_EL] >> strip_tac >>
     qpat_x_assum `!n. n < LENGTH h ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_paired_cursor lp a at` by
    (drule_all (Q.INST [`j` |-> `q`] ptr_paired_prefix_alignment) >>
     fs[EL_APPEND_EQN]) >>
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  drule_all ptr_departed_cursor_instruction >>
  simp[concretize_positions_unchanged]
QED

(* Join actual call edges to the production stage and its callee entry shape. *)
Theorem ptr_dalloca_historical_runtime_call:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht endpoint_t done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n = EL q done /\
  a = EL n h /\ at = EL q ht /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  EL n H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  b = EL (SUC n) h /\ bt = EL (SUC q) ht /\
  ptr_tagged_chrono_step C (HD tsj) a b PTj TGj sj PTj' TGj' sj' /\
  ptr_chrono_step C' at bt /\
  a.po_inst.inst_opcode = INVOKE /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TGj v = NONE) /\
  (!v site. FLOOKUP TGj v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
     FLOOKUP at.po_prov v = SOME site) ==>
  ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TGj' v = NONE) /\
  (!v site. FLOOKUP TGj' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site) /\
  LENGTH PTj' = LENGTH b.po_params /\
  LENGTH b.po_params = LENGTH bt.po_params /\
  (!k site. k < LENGTH b.po_params ==>
    (EL k bt.po_params = SOME site ==>
      EL k b.po_params = SOME site /\ EL k PTj' = NONE /\
      EL k b.po_state.vs_params = EL k bt.po_state.vs_params) /\
    (EL k PTj' = NONE /\ EL k b.po_params = SOME site ==>
      EL k bt.po_params = SOME site)) /\
  sj' = (PTj,TGj)::sj /\
  b.po_stack =
    <| cf_fn := a.po_fn; cf_inst := a.po_inst; cf_state := a.po_state;
       cf_params := a.po_params; cf_prov := a.po_prov;
       cf_tvar := a.po_taint.t_var |> :: a.po_stack /\
  bt.po_stack =
    <| cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var |> :: at.po_stack
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.po_inst.inst_opcode <> ALLOCA` by simp[] >>
  drule_all ptr_dalloca_historical_control_inst >> strip_tac >>
  mp_tac ptr_stage_paired_bridge >>
  (impl_tac >-
    (rpt conj_tac >> asm_rewrite_tac[] >>
     qexists_tac `names` >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `bridge_R` (qx_choose_then `bridge_lp`
    (qx_choose_then `bridge_positions` (map_every assume_tac o CONJUNCTS)))) >>
  `!name fn. lookup_function name C.ctx_functions = SOME fn ==>
    first_block_no_phi fn` by
    (rpt strip_tac >> imp_res_tac lookup_function_MEM >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `!name fn. lookup_function name C'.ctx_functions = SOME fn ==>
    first_block_no_phi fn` by
    (rpt strip_tac >>
     `?source. lookup_function name C.ctx_functions = SOME source /\
       ptr_paired_code bridge_R bridge_lp bridge_positions source fn` by
       (drule_all list_rel_lookup_function >>
        disch_then (qspec_then `name` mp_tac) >>
        Cases_on `lookup_function name C.ctx_functions` >> simp[]) >>
     `wf_function source /\ first_block_no_preds source /\
       first_block_no_phi source` by
       (imp_res_tac lookup_function_MEM >>
        fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
     mp_tac (Q.INST [`p` |-> `bridge_lp (source:ir_function)`,
       `fn` |-> `source:ir_function`]
       concretize_positions_first_block) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     fs[ptr_paired_code_def, first_block_no_phi_def]) >>
  mp_tac (Q.INST [`Ct` |-> `C'`, `token` |-> `HD tsj`,
    `PT` |-> `PTj`, `TG` |-> `TGj`, `saved` |-> `sj`,
    `PT'` |-> `PTj'`, `TG'` |-> `TGj'`, `saved'` |-> `sj'`]
    ptr_dalloca_runtime_chrono_call) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* Restore the actual saved heads at the departed return instruction. *)
Theorem ptr_dalloca_historical_runtime_ret:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht endpoint_t done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n = EL q done /\
  a = EL n h /\ at = EL q ht /\
  EL n H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  b = EL (SUC n) h /\ bt = EL (SUC q) ht /\
  ptr_tagged_chrono_step C (HD tsj) a b PTj TGj sj PTj' TGj' sj' /\
  ptr_chrono_step C' at bt /\
  a.po_stack = f::stk /\ at.po_stack = ft::stkt /\
  sj = (RPT,RTG)::tail /\
  is_raw_return_opcode a.po_inst.inst_opcode /\
  ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
    ft.cf_prov ft.cf_tvar ft.cf_state /\
  (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP RTG v = NONE) /\
  (!v site. FLOOKUP RTG v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
     FLOOKUP ft.cf_prov v = SOME site) /\
  f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
  LENGTH RPT = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
  (!k site. k < LENGTH f.cf_params ==>
    (EL k ft.cf_params = SOME site ==>
      EL k f.cf_params = SOME site /\ EL k RPT = NONE /\
      EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
    (EL k RPT = NONE /\ EL k f.cf_params = SOME site ==>
      EL k ft.cf_params = SOME site)) ==>
  ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TGj' v = NONE) /\
  (!v site. FLOOKUP TGj' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site) /\
  PTj' = RPT /\ sj' = tail /\
  b.po_stack = stk /\ bt.po_stack = stkt /\
  LENGTH PTj' = LENGTH b.po_params /\
  LENGTH b.po_params = LENGTH bt.po_params /\
  (!k site. k < LENGTH b.po_params ==>
    (EL k bt.po_params = SOME site ==>
      EL k b.po_params = SOME site /\ EL k PTj' = NONE /\
      EL k b.po_state.vs_params = EL k bt.po_state.vs_params) /\
    (EL k PTj' = NONE /\ EL k b.po_params = SOME site ==>
      EL k bt.po_params = SOME site))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.po_inst.inst_opcode <> ALLOCA` by fs[is_raw_return_opcode_def] >>
  drule_all ptr_dalloca_historical_control_inst >> strip_tac >>
  mp_tac (Q.INST [`Ct` |-> `C'`, `token` |-> `HD tsj`,
    `PT` |-> `PTj`, `TG` |-> `TGj`, `saved` |-> `sj`,
    `PT'` |-> `PTj'`, `TG'` |-> `TGj'`, `saved'` |-> `sj'`]
    ptr_dalloca_runtime_chrono_ret) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
