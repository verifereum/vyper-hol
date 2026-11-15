Theory readonlyInvokeCopyFwdExecutionEntry
Ancestors
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdOpaqueReturn readonlyInvokeCopyFwdOpaquePhi
  readonlyInvokeCopyFwdHeterogeneousLifecycle readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHistoryOperandOrigins
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdAnalyzedLifecycle
  readonlyInvokeCopyFwdExecutionHistoryLifecycle
  occurrenceGeometry occurrenceOrigin
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  internalReturnCopyFwdSim frameRel unitShapeDefs o1PassContract
  ptrDiscipline taintAgree contextCodegenRel allocaFrontierBound
  venomExecSemantics venomState venomInst venomWf venomWfProps finite_map list pred_set

Theorem ricf_opaque_params_cons[local]:
  ricf_opaque_params_agree sites (p::PG) (x::xs) (y::ys) <=>
  ricf_opaque_value_agree sites p {} x y /\
  ricf_opaque_params_agree sites PG xs ys
Proof
  simp[ricf_opaque_params_agree_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> Cases >> simp[]
QED

Theorem ricf_opaque_clean_args[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  !ops args.
    eval_operands ops s = SOME args /\
    (!op. MEM op ops ==> op_taint tn op = {} /\
      !v. op = Var v ==> ~retpc_var fn v) ==>
    ?args'. eval_operands ops t = SOME args' /\
      ricf_opaque_params_agree sites (MAP (op_prov G) ops) args args'
Proof
  strip_tac >> Induct
  >- simp[eval_operands_def, ricf_opaque_params_agree_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_operand h s` >- gvs[eval_operands_def] >>
  rename1 `eval_operand h s = SOME value` >>
  Cases_on `eval_operands ops s` >- gvs[eval_operands_def] >>
  rename1 `eval_operands ops s = SOME values` >>
  `op_taint tn h = {} /\ (!v. h = Var v ==> ~retpc_var fn v)` by
    fs[] >>
  `?y. eval_operand h t = SOME y /\
    ricf_opaque_value_agree sites (op_prov G h) {} value y` by
    (drule_all ricf_opaque_frame_operand >> gvs[]) >>
  `?ys. eval_operands ops t = SOME ys /\
    ricf_opaque_params_agree sites (MAP (op_prov G) ops) values ys` by
    (qpat_x_assum `!args. _` irule >> simp[] >> metis_tac[MEM]) >>
  qexists_tac `y::ys` >> gvs[eval_operands_def, ricf_opaque_params_cons]
QED

Theorem ricf_execution_unchanged_call_args[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  eval_operands ops s = SOME args ==>
  ?args'. eval_operands ops t = SOME args' /\
    ricf_opaque_params_agree sites (MAP (op_prov G) ops) args args'
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s /\ MEM inst (fn_insts fn)` by
    metis_tac[ptr_discipline_def, active_inst_mem_fn_insts] >>
  `!op. MEM op ops ==> op_taint tn op = {} /\
    !v. op = Var v ==> ~retpc_var fn v` by
    (qx_gen_tac `op` >> strip_tac >>
     `MEM op inst.inst_operands` by
       (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
     conj_tac
     >- metis_tac[taint_ok_invoke_operand] >>
     qx_gen_tac `v` >> strip_tac >>
     fs[opaque_use_ok_def, retpc_use_ok_def] >>
     qpat_x_assum `!inst' x. _` (qspecl_then [`inst`,`v`] mp_tac) >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule ricf_opaque_clean_args >>
  disch_then (qspecl_then [`ops`,`args`] mp_tac) >> simp[] >>
  disch_then irule >> rpt strip_tac >> metis_tac[]
QED

Theorem ricf_opaque_call_stack[local]:
  ricf_opaque_frame_agree caller D (ircf_dead ids s stk) sites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  setup_callee callee args s = SOME cs /\
  setup_callee callee args' t = SOME ct ==>
  ricf_opaque_live_stack_agree D ids (tn with t_var := FEMPTY)
    (sites::maps) (f::stk) (t::targets) cs ct
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[ricf_opaque_live_stack_cons] >>
  gvs[ricf_opaque_live_stack_agree_def, merge_callee_state_def]
QED

Theorem ricf_execution_call_outer[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C ==>
  DRESTRICT B {id | FST id <> n} = B /\
  {id | id IN E /\ FST id <> n} = E
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  drule occ_frame_reachable_annotation >>
  simp[occurrence_annotation_ok_def] >> strip_tac >>
  `!id. id IN FDOM B ==> FST id < n` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!id. id IN E ==> id IN FDOM B` by
    (rpt strip_tac >>
     fs[ricf_execution_invariant_def, ricf_heterogeneous_support_origins_def] >>
     qpat_x_assum `!id. id IN E ==> _` (qspec_then `id` mp_tac) >>
     simp[] >> strip_tac >> fs[FLOOKUP_DEF]) >>
  `!id. id IN FDOM B ==> FST id <> n` by
    (rpt strip_tac >> `FST id < n` by metis_tac[] >> decide_tac) >>
  conj_tac
  >- (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >> qx_gen_tac `id` >>
      Cases_on `FLOOKUP B id` >> simp[] >>
      `FST id <> n` by (fs[FLOOKUP_DEF] >> metis_tac[]) >> simp[]) >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem ricf_execution_call_entry:
  ricf_execution_invariant vs C D stk PG G tn caller callinst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn caller callinst s a U B history sites maps /\
  ricf_history_certificates vs C log_of stk PG G tn caller callinst s a U B
    history certificates /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\ ptr_discipline lo C vs /\
  ricf_full_alloca_copies caller /\ ricf_src_alloca caller /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  setup_callee callee args' t = SOME ct /\
  ricf_opaque_params_agree callsites (MAP (op_prov G) ops) args args' /\
  ricf_sites_ok callsites /\ ircf_cross tn (ricf_site_triples callsites) s t /\
  ricf_mapped_support n B E (MAP (op_prov G) ops) FEMPTY callsites /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  u = <|of_owner := a; of_prov := H; of_params := HP|> /\
  (!s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ricf_heterogeneous_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B callsites /\
    ricf_analyzed_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B callsites) ==>
  ricf_execution_boundary vs C mid_of log_of D n (u::U) B E
    (ricf_phase_push f history) (ricf_phase_push f certificates) callsites (sites::maps) (t::targets)
    (f::stk) (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY)
    callee cs ct
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn caller callinst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `frame_reachable vs C stk PG G tn caller callinst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM caller C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
   wf_function caller /\ ssa_form caller /\ fn_inst_wf caller /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts caller))` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_ssa_def,
        wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
        fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry, ptr_discipline_def] >>
  `occurrence_syntax_origin caller a H` by
    metis_tac[occ_frame_reachable_origin_certificate,
      occurrence_origin_certificate_current] >>
  `DRESTRICT B {id | FST id <> n} = B /\ {id | id IN E /\ FST id <> n} = E` by
    (irule ricf_execution_call_outer >> metis_tac[]) >>
  `ricf_opaque_frame_agree caller D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (tn with t_var := FEMPTY) (sites::maps) (f::stk) (t::targets) cs ct` by
    (irule ricf_opaque_call_stack >> fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `ricf_opaque_frame_agree callee D (ircf_dead (ricf_original_copy_ids C) cs (f::stk))
    callsites (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) cs ct` by
    (`ircf_dead (ricf_original_copy_ids C) cs (f::stk) =
      ircf_dead (ricf_original_copy_ids C) s stk` by
       (irule ricf_live_callee_dead >> simp[] >> metis_tac[]) >>
     drule_all ricf_opaque_setup_callee_frame >> gvs[]) >>
  `ricf_support_agree B E (tn with t_var := FEMPTY) cs ct /\
   ricf_cert_crosses (tn with t_var := FEMPTY)
     (ricf_phase_stack_ranges (f::stk) (ricf_phase_push f certificates)) (f::stk) cs ct` by
    (fs[ricf_execution_invariant_def] >>
     gvs[setup_callee_def, AllCaseEqs(), ricf_support_agree_def,
       ricf_phase_stack_ranges_push, ricf_cert_crosses_cons,
       ricf_cert_crosses_def, ircf_cross_def, EVERY_MEM] >> metis_tac[]) >>
  `!s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ricf_heterogeneous_saved_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B (sites::maps)` by
    (rpt strip_tac >> irule ricf_heterogeneous_saved_map_origins_call >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  simp[ricf_execution_boundary_def] >> rpt strip_tac >>
  `retpc_shape_ok callee /\ fn_inst_wf callee` by
    fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `s1 = cs /\ entry_prov callee cs FEMPTY = FEMPTY /\
   entry_taint_vars callee cs (tn with t_var := FEMPTY) =
     (tn with t_var := FEMPTY)` by
    (qpat_x_assum `enters_block callee cs s1` mp_tac >>
     simp[enters_block_def] >> strip_tac >>
     `cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0` by
       gvs[setup_callee_def, AllCaseEqs()] >>
     namedCases_on `bb.bb_instructions` ["", "first rest"] >>
     gvs[eval_phis_def, phi_prefix_length_def, entry_prov_def,
       phis_prov_def, entry_taint_vars_def, phis_taint_def] >>
     Cases_on `first.inst_opcode = PHI` >>
     gvs[eval_phis_def, eval_one_phi_def, phi_prefix_length_def,
       phis_prov_def, phis_taint_def, AllCaseEqs()]) >>
  `ircf_cross (tn with t_var := FEMPTY) {} cs ct` by simp[ircf_cross_def] >>
  drule_all ricf_opaque_live_support_enters_block >> strip_tac >>
  `ricf_heterogeneous_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B callsites /\
   ricf_analyzed_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B callsites` by
    metis_tac[] >>
  `ricf_analyzed_origins vs C (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 n (u::U) B
    (ricf_phase_push f history) callsites (sites::maps)` by
    (simp[ricf_analyzed_origins_def] >> rpt conj_tac
     >- (irule ricf_analyzed_ledger_call >>
         fs[ricf_analyzed_origins_def] >> metis_tac[])
     >>
     irule ricf_analyzed_saved_map_origins_call >>
     fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
  `ricf_chosen_support vs C log_of n callee B E` by
    (`!id. id IN E ==> FST id <> n` by
       (fs[EXTENSION] >> metis_tac[]) >>
     simp[ricf_chosen_support_def] >> metis_tac[]) >>
  `ricf_history_certificates vs C log_of (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 n (u::U) B
    (ricf_phase_push f history) (ricf_phase_push f certificates)` by
    (drule_all ricf_history_certificates_call >> simp[]) >>
  qexistsl_tac [`t1`,`SUC n`,`B`,`MAP (op_prov H) ops`,`FEMPTY`,
    `ricf_phase_push f history`,`ricf_phase_push f certificates`,`E`] >>
  simp[ricf_phase_push_outer] >> conj_tac
  >- metis_tac[ricf_function_edit_enters_block] >>
  `cs.vs_prev_bb = NONE /\ cs.vs_params = args` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  `LENGTH (MAP (op_prov G) ops) = LENGTH args` by
    fs[ricf_opaque_params_agree_def] >>
  simp[ricf_execution_invariant_def] >> rpt conj_tac
  >- (irule ricf_heterogeneous_source_ledger_call >>
      fs[ricf_execution_invariant_def] >> metis_tac[])
  >- gvs[ricf_complete_params_def]
  >- gvs[]
  >- simp[ricf_phase_ranges_push_current, ircf_cross_def]
  >- gvs[]
  >- (irule ricf_heterogeneous_support_call >>
      fs[ricf_execution_invariant_def] >> metis_tac[])
  >- gvs[]
  >- gvs[]
  >> gvs[ricf_execution_invariant_def, ricf_mapped_support_def] >> metis_tac[]
QED

Theorem ricf_execution_unchanged_call_entry:
  ricf_execution_invariant vs C D stk PG G tn caller callinst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn caller callinst s a U B history sites maps /\
  ricf_history_certificates vs C log_of stk PG G tn caller callinst s a U B
    history certificates /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ricf_full_alloca_copies caller /\ ricf_src_alloca caller /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  opaque_use_ok caller /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ricf_mapped_support n B E (MAP (op_prov G) ops) FEMPTY sites /\
  o1_fn_shape C callee /\ ricf_function_edit callee (mid_of callee) /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  u = <|of_owner := a; of_prov := H; of_params := HP|> ==>
  ?args' ct. eval_operands ops t = SOME args' /\
    setup_callee callee args' t = SOME ct /\
    ricf_execution_boundary vs C mid_of log_of D n (u::U) B E
      (ricf_phase_push f history) (ricf_phase_push f certificates) sites (sites::maps) (t::targets)
      (f::stk) (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY)
      callee cs ct
Proof
  strip_tac >> drule_all ricf_execution_unchanged_call_args >> strip_tac >>
  `?ct. setup_callee callee args' t = SOME ct` by
    (gvs[setup_callee_def, AllCaseEqs()] >> metis_tac[]) >>
  qexistsl_tac [`args'`,`ct`] >> simp[] >>
  `ricf_sites_ok sites /\ ircf_cross tn (ricf_site_triples sites) s t` by
    fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
  `!s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ricf_heterogeneous_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B sites /\
    ricf_analyzed_map_origins vs C (f::stk) (MAP (op_prov G) ops)
      FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B sites` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (irule ricf_heterogeneous_map_origins_call >>
         fs[ricf_execution_invariant_def] >> metis_tac[]) >>
     irule ricf_analyzed_map_origins_call >>
     fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
  drule_all ricf_execution_call_entry >> simp[]
QED
