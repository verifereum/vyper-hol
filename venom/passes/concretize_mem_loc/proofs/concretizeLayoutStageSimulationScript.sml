Theory concretizeLayoutStageSimulation
Ancestors
  concretizeLayoutCutSafe frameGasEvents gasEvents concretizeLayoutCanonicalContract concretizeLayoutStageEntry
  frameSelectedSimulation frameDecorationComplete frameResolvedCoherent frameFiniteJointDecoration frameJointTrace
  frameSelectedDecoration list concretizePtrParamShape unitTransformDefs o1PassContract
  ptrDiscipline venomExecSemantics passSimulationDefs frameFiniteExecution frameFiniteJointTrace
  frameJointTransition venomWf contextCodegenRel o1ContractSimplifyCfg concretizeStepStructure
  concretizeLayoutCanonicalDriver concretizeLayoutStagePairing concretizeMemLocDefs concretizeLayoutCanonicalPrefix frameSelectedPrefix
  frameDecoratedPrefix frameFinitePrefix o1SafeUpto rich_list concretizeLayoutCanonicalBaseTerminalExit
  passSharedFrame passSharedDefs concretizeLayoutCanonicalCallEntry concretizeLayoutSelectedBaseInterface concretizeLayoutCanonicalBlock
  concretizeLayoutCanonicalDeferred concretizeLayoutCanonicalRunNext

(* The generic selected driver is the only recursive simulation used here. *)
Theorem layout_stage_selected_run_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\
  layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend /\
  decorated_run C fn s r q n w qe d /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
  run_blocks fuel C fn s = r ==>
  ?r'. run_blocks fuel C' fn' t = r' /\ finite_run C' fn' t r' /\
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r' /\
    run_events_agree C C' fn s fn' t r r'
Proof
  strip_tac >>
  `selected_simulation_contract_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))` by
    (irule layout_canonical_simulation_contract_fuel >> metis_tac[]) >>
  drule_all selected_run_simulation_fuel >> simp[selected_run_match_fuel_def, events_OutR_def]
QED

Theorem layout_stage_selected_run:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\
  layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend /\
  decorated_run C fn s r q n w qe d /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  ?r'. finite_run C' fn' t r' /\
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r' /\
    run_events_agree C C' fn s fn' t r r'
Proof
  strip_tac >>
  `finite_run C fn s r` by metis_tac[cj 3 decorated_execution_erases] >>
  `?fuel. run_blocks fuel C fn s = r` by
    (fs[finite_run_iff] >> metis_tac[]) >>
  drule_all layout_stage_selected_run_fuel >> metis_tac[]
QED

(* Empty-revert observation on the prescribed selected executions. *)
Theorem layout_selected_empty_induction[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend ==>
  (!K i s r q n w qe d. decorated_step K i s r q n w qe d ==>
    !fuel j t g fin tfin. K = C /\
      selected_segment C q0 path n q w qe /\
      layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
        q n i s j t (INL g) /\
      step_inst fuel C i s = r /\ step_inst fuel C' j t = Abort Revert_abort tfin /\
      r = Abort Revert_abort fin /\ fin.vs_returndata = [] ==>
      tfin.vs_returndata = []) /\
  (!K bb s r q n w qe d. decorated_block K bb s r q n w qe d ==>
    !fuel bb' t g fin tfin. K = C /\
      selected_segment C q0 path n q w qe /\
      layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
        q n bb s bb' t (INL g) /\ layout_paired_prefix_alias bb s bb' t /\
      exec_block fuel C bb s = r /\ exec_block fuel C' bb' t = Abort Revert_abort tfin /\
      r = Abort Revert_abort fin /\ fin.vs_returndata = [] ==>
      tfin.vs_returndata = []) /\
  (!K fn s r q n w qe d. decorated_run K fn s r q n w qe d ==>
    !fuel fn' t fin tfin. K = C /\
      selected_segment C q0 path n q w qe /\
      layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
      run_blocks fuel C fn s = r /\ run_blocks fuel C' fn' t = Abort Revert_abort tfin /\
      r = Abort Revert_abort fin /\ fin.vs_returndata = [] ==>
      tfin.vs_returndata = [])
Proof
  strip_tac >> ho_match_mp_tac decorated_step_strongind >> rpt conj_tac
  >- suspend "base"
  >- (rpt strip_tac >> gvs[])
  >- suspend "invoke_exit"
  >- (rpt strip_tac >> gvs[AllCaseEqs()])
  >- suspend "block_next"
  >- suspend "block_exit"
  >- suspend "run_next"
  >- (rpt strip_tac >> gvs[])
  >> suspend "run_exit"
QED

Resume layout_selected_empty_induction[base]:
  rpt strip_tac >> gvs[] >>
  Cases_on `i.inst_opcode = REVERT`
  >- (irule layout_canonical_ordinary_revert_empty >> metis_tac[]) >>
  `j.inst_opcode <> REVERT /\ j.inst_opcode <> INVOKE` by
    (fs[layout_canonical_step_witness_def] >>
     Cases_on `i.inst_opcode = ALLOCA` >>
     gvs[concretize_inst_with_positions_def, AllCaseEqs(),
         mk_assign_inst_def, mk_nop_inst_def]) >>
  fs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_nonrevert_revert_empty]
QED
Resume layout_selected_empty_induction[invoke_exit]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `joint_segment C q' w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path)
     ass qend q n i s j t` by
    (simp[layout_canonical_ES_def, layout_base_lookahead_def] >> metis_tac[]) >>
  `j = i /\ ?out ct phase.
    lookup_function name C'.ctx_functions = SOME out /\
    (?args'. eval_operands ops t = SOME args' /\ setup_callee out args' t = SOME ct) /\
    layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      ass qend q' (n+1) fn s'' out ct /\
    layout_driver_indexed (MAP FST path) ass phase /\ ~phase.lop_pending /\
    phase.lop_config = q /\ phase.lop_cursor = n /\
    layout_ordinary_entry D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      qend phase s t /\ control_agree s t` by
    (irule layout_canonical_call_entry >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `selected_segment C q0 path (phase.lop_cursor+1) q' w qe` by
    (`selected_segment C q0 path phase.lop_cursor phase.lop_config [(NONE,q')] q' /\
      selected_segment C q0 path
        (phase.lop_cursor + LENGTH ([(NONE,q')]:(origin_event option # joint_config) list)) q' w qe` by
       (irule selected_segment_parts >> gvs[joint_segment_def]) >> fs[]) >>
  fs[step_inst_def, AllCaseEqs()] >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED
Resume layout_selected_empty_induction[block_next]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `finite_step C i s (OK post)` by metis_tac[decorated_execution_erases] >>
  `step_inst fuel C i s = OK post` by
    (irule finite_block_step_fuel_inv >> simp[] >>
     qexists `bb` >> simp[]) >>
  `?j. layout_canonical_step_witness D lo vs0 C C' q0 (MAP FST path)
      (MAP SND path) ass qend q n i s j t (INL g) /\
      (i.inst_opcode <> NOP ==> get_instruction bb' t.vs_inst_idx = SOME j)` by
    metis_tac[layout_canonical_block_witness_step] >>
  `joint_segment C q w qe /\ joint_segment C q' w' qe'` by
    metis_tac[decorated_execution_segment] >>
  `selected_segment C q0 path n q w qe /\
   selected_segment C q0 path (n+LENGTH w+1) q' w' qe'` by
    (`joint_segment C qe ([(ev,q')]++w') qe'` by
       gvs[joint_segment_def, decoration_consumes_def] >>
     `selected_segment C q0 path n q w qe /\
      selected_segment C q0 path (n+LENGTH w) qe ([(ev,q')]++w') qe'` by
       (irule selected_segment_parts >> fs[APPEND_ASSOC]) >>
     `joint_segment C qe [(ev,q')] q'` by
       gvs[joint_segment_def, decoration_consumes_def] >>
     drule_all selected_segment_parts >> simp[] >> metis_tac[]) >>
  `layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path)
     ass qend q n i s j t` by
    (simp[layout_canonical_ES_def] >>
     conj_tac >- (irule layout_base_lookahead_next >> metis_tac[]) >>
     metis_tac[]) >>
  `selected_simulation_contract_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)` by
    (irule layout_canonical_simulation_contract_fuel >> simp[] >> metis_tac[]) >>
  `?rs. step_inst fuel C' j t = rs /\ finite_step C' j t rs /\
    layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend
      q n qe (n+LENGTH w) i s j t (OK post) rs` by
    (simp[GSYM selected_step_match_fuel_def] >>
     irule (cj 1 selected_simulation_induction_fuel) >> metis_tac[]) >>
  `?tp. rs = OK tp` by
    (Cases_on `rs` >>
     gvs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def]) >>
  gvs[] >>
  Cases_on `i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s`
  >- suspend "forward" >>
  `?b tb. layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
      (MAP SND path) ass qend q' (n+LENGTH w+1) bb
      (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb (INL b) /\
    layout_paired_prefix_alias bb (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
    tb = (if i.inst_opcode = NOP then t else tp with vs_inst_idx := SUC t.vs_inst_idx) /\
    (!k rb. step_inst k C' j t = OK tp /\ exec_block k C' bb' tb = rb ==>
      exec_block k C' bb' t = rb)` by
    (irule layout_canonical_prefix_next_ordinary >> simp[] >> metis_tac[]) >>
  `exec_block fuel C bb (post with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort fin` by
    (qpat_x_assum `exec_block fuel C bb s = _` mp_tac >> simp[Once exec_block_def]) >>
  `exec_block fuel C' bb' tb = Abort Revert_abort tfin` by
    (Cases_on `i.inst_opcode = NOP` >- gvs[] >>
     gvs[] >> qpat_x_assum `exec_block fuel C' bb' t = _` mp_tac >>
     simp[Once exec_block_def]) >>
  first_x_assum irule >> qexistsl [`bb'`, `fuel`, `b`, `tb`] >> gvs[]
QED
Resume layout_selected_empty_induction[forward]:
  `g.lop_origin.lbo_source = bb /\ g.lop_origin.lbo_target = bb'` by
    fs[layout_canonical_block_witness_def,
       concretizeLayoutPairedEntryTheory.layout_paired_ordinary_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (fs[layout_canonical_block_witness_def, decoration_entry_def] >>
     Cases_on `q` >> gvs[decoration_at_def]) >>
  `?jidx term opd ops opn ptr_op len.
    revert_forward_pair bb s.vs_inst_idx jidx /\
    get_instruction bb jidx = SOME term /\ term.inst_operands = [ptr_op;len] /\
    i.inst_operands = [opd;ops;opn]` by
    (fs[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     gvs[] >> metis_tac[]) >>
  `step_inst_base i s = OK post` by
    (gvs[step_inst_non_invoke]) >>
  `?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      ass qend n F (INL g) post tpost /\ tfin.vs_returndata = []` by
    (irule layout_forward_block_revert_empty >> gvs[] >> metis_tac[]) >>
  simp[]
QED
Resume layout_selected_empty_induction[block_exit]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `finite_step C i s (Abort Revert_abort fin)` by metis_tac[decorated_execution_erases] >>
  `step_inst fuel C i s = Abort Revert_abort fin` by
    (irule finite_block_step_fuel_inv >> simp[] >> qexists `bb` >> simp[]) >>
  `i.inst_opcode <> NOP` by
    (strip_tac >> qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once decorated_step_cases, step_inst_base_def]) >>
  drule_all layout_canonical_block_witness_step >> strip_tac >>
  `layout_base_lookahead C q0 path q n i s` by
    (irule layout_base_lookahead_exit >>
     qexistsl [`d`, `qe`, `Abort Revert_abort fin`, `w`] >> simp[]) >>
  `layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path)
    ass qend q n i s j t` by (simp[layout_canonical_ES_def] >> metis_tac[]) >>
  `selected_simulation_contract_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)` by
    (irule layout_canonical_simulation_contract_fuel >> simp[] >> metis_tac[]) >>
  `?rs. step_inst fuel C' j t = rs /\ finite_step C' j t rs /\
    layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend
      q n qe (n+LENGTH w) i s j t (Abort Revert_abort fin) rs` by
    (simp[GSYM selected_step_match_fuel_def] >>
     irule (cj 1 selected_simulation_induction_fuel) >> metis_tac[]) >>
  `?ts. rs = Abort Revert_abort ts` by
    (Cases_on `i.inst_opcode = INVOKE` >> Cases_on `rs` >>
     gvs[layout_deferred_OS_def, layout_canonical_OS_def, layout_canonical_result_def,
         dead_result_rel_def]) >>
  gvs[] >>
  `ts = tfin` by
    (qpat_x_assum `exec_block fuel C' bb' t = _` mp_tac >>
     simp[Once exec_block_def]) >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED
Resume layout_selected_empty_induction[run_next]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all layout_canonical_run_block_entry_prefix >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC]) >>
  drule_all (PURE_REWRITE_RULE[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] selected_run_next_children) >>
  strip_tac >>
  `?h. fuel' = SUC h /\ exec_block h C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s''` by
    (irule finite_run_block_fuel_inv >> conj_tac
     >- (qexistsl [`fn`, `Abort Revert_abort fin`, `s`] >> simp[]) >>
     metis_tac[decorated_execution_erases]) >>
  gvs[] >>
  `selected_simulation_contract_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)` by
    (irule layout_canonical_simulation_contract_fuel >> simp[] >> metis_tac[]) >>
  `?rb. run_block_non_phis h' C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = rb /\
    finite_block C' bb' (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) rb /\
    layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend
      q n (JointConfig stk PG G tn fn i si oms om hs h) (n+LENGTH w)
      bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      bb' (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) (OK s'') rb` by
    (simp[GSYM selected_block_match_fuel_def] >>
     irule (cj 2 selected_simulation_induction_fuel) >> metis_tac[]) >>
  `?v. rb = OK v` by
    (Cases_on `rb` >> gvs[layout_canonical_OB_def, layout_canonical_result_def]) >>
  gvs[] >>
  `layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend
    (EL (n+(LENGTH w+1)) (q0::MAP SND path)) (n+(LENGTH w+1)) fn s'' fn' v` by
    (irule (PURE_REWRITE_RULE[GSYM arithmeticTheory.ADD_ASSOC] layout_canonical_run_continue) >>
     simp[] >> metis_tac[]) >>
  `~v.vs_halted` by metis_tac[frameFiniteControlTheory.finite_execution_block_endpoint] >>
  `run_blocks h' C fn s'' = Abort Revert_abort fin /\
   run_blocks h' C' fn' v = Abort Revert_abort tfin` by
    (conj_tac
     >- (qpat_x_assum `run_blocks (SUC h') C fn s = _` mp_tac >>
         simp[Once run_blocks_def, run_block_def]) >>
     qpat_x_assum `run_blocks (SUC h') C' fn' t = _` mp_tac >>
     simp[Once run_blocks_def, run_block_def]) >>
  first_x_assum irule >> simp[] >>
  fs[selected_run_def] >> metis_tac[]
QED
Resume layout_selected_empty_induction[run_exit]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all layout_canonical_run_block_entry_prefix >> strip_tac >>
  `?h. fuel = SUC h /\ exec_block h C bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Abort Revert_abort fin` by
    (irule finite_run_block_fuel_inv >> conj_tac
     >- (qexistsl [`fn`, `Abort Revert_abort fin`, `s`] >> simp[]) >>
     metis_tac[decorated_execution_erases]) >> gvs[] >>
  `selected_simulation_contract_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_run D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend)` by
    (irule layout_canonical_simulation_contract_fuel >> simp[] >> metis_tac[]) >>
  `?rb. run_block_non_phis h C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = rb /\
    finite_block C' bb' (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) rb /\
    layout_canonical_OB D lo vs0 C C' q0 (MAP FST path) (MAP SND path) ass qend
      q n qe (n+LENGTH w)
      bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      bb' (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
      (Abort Revert_abort fin) rb` by
    (simp[GSYM selected_block_match_fuel_def] >>
     irule (cj 2 selected_simulation_induction_fuel) >> metis_tac[]) >>
  `?ts. rb = Abort Revert_abort ts` by
    (Cases_on `rb` >> gvs[layout_canonical_OB_def, layout_canonical_result_def,
      dead_result_rel_def]) >> gvs[] >>
  `run_block_non_phis h C' bb'
    (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = Abort Revert_abort tfin` by
    (qpat_x_assum `run_blocks (SUC h) C' fn' t = _` mp_tac >>
     simp[Once run_blocks_def, run_block_def] >>
     Cases_on `exec_block h C' bb'
       (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED
Finalise layout_selected_empty_induction

Theorem layout_stage_selected_run_fuel_revert_empty:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend /\
  decorated_run C fn s r q n w qe d /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
  run_blocks fuel C fn s = r ==>
  ?r'. run_blocks fuel C' fn' t = r' /\ finite_run C' fn' t r' /\
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r' /\
    (!post tpost. r = Abort Revert_abort post /\ r' = Abort Revert_abort tpost /\
      post.vs_returndata = [] ==> tpost.vs_returndata = [])
Proof
  strip_tac >> drule_all layout_stage_selected_run_fuel >> strip_tac >>
  qexists `r'` >> simp[] >> rpt strip_tac >>
  irule (cj 3 layout_selected_empty_induction) >> metis_tac[]
QED

Theorem layout_segment_chain[local]:
  !w q qe. joint_segment C q w qe ==>
    joint_chain C q (MAP FST w) (MAP SND w) qe
Proof
  Induct >> simp[joint_segment_def, joint_chain_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[joint_segment_def, joint_chain_def] >> metis_tac[]
QED

(* A source segment from the initial config is a joint trace with one
   coherent annotation sequence. *)
Theorem layout_stage_segment_annotations[local]:
  joint_segment C q0 w qe /\ joint_initial vs0 C q0 /\ ~ctx_has_dalloca C ==>
  ?ass.
    selected_segment C q0 w 0 q0 w qe /\
    joint_trace vs0 C q0 (MAP FST w) (MAP SND w) qe /\
    EL 0 ass = [([],FEMPTY)] /\
    (!k. k < LENGTH w ==>
      resolved_annotation_edge C k (EL k (q0::MAP SND w)) (FST (EL k w))
        (EL (SUC k) (q0::MAP SND w))
        (EL k (lifetime_annotations 0 [0] (MAP FST w))) (EL k ass)
        (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST w)))
        (EL (SUC k) ass))
Proof
  strip_tac >>
  `joint_trace vs0 C q0 (MAP FST w) (MAP SND w) qe` by
    (simp[joint_trace_def] >> metis_tac[layout_segment_chain]) >>
  drule_all joint_trace_coherent_annotations >> strip_tac >>
  qexists `ass` >> simp[] >>
  simp[selected_segment_def, joint_segment_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  simp[EL_MAP]
QED

(* One ambient source decoration and one coherent annotation sequence. *)
Theorem layout_stage_source_decoration:
  finite_run C fn s r /\ enters_block fn s p /\
  joint_initial vs0 C q0 /\ decoration_entry fn p q0 /\
  ALL_DISTINCT (fn_labels fn) /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions /\
  ~ctx_has_dalloca C ==>
  ?path qe d ass.
    decorated_run C fn s r q0 0 path qe d /\
    selected_segment C q0 path 0 q0 path qe /\
    joint_trace vs0 C q0 (MAP FST path) (MAP SND path) qe /\
    EL 0 ass = [([],FEMPTY)] /\
    (!k. k < LENGTH path ==>
      resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
        (EL (SUC k) (q0::MAP SND path))
        (EL k (lifetime_annotations 0 [0] (MAP FST path))) (EL k ass)
        (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST path)))
        (EL (SUC k) ass))
Proof
  strip_tac >> drule (cj 3 finite_decoration_complete) >>
  disch_then (qspecl_then [`q0`, `0`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  `joint_segment C q0 w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_stage_segment_annotations >> strip_tac >>
  qexistsl [`w`, `qe`, `d`, `ass`] >> fs[]
QED

(* Root entry: the target run terminates with the source's GAS events. *)
Theorem layout_stage_terminating_events:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  terminates (run_context fuel C vs) ==>
  ?fuel' name fn fn' lbl.
    C.ctx_entry = SOME name /\ C'.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME lbl /\ fn_entry_label fn' = SOME lbl /\
    dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs) /\
    terminates (run_context fuel' C' vs) /\
    gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
    gas_events_blocks fuel C fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `?name fn lbl. C.ctx_entry = SOME name /\
     lookup_function name C.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl` by
    (qpat_x_assum `terminates _` mp_tac >>
     Cases_on `C.ctx_entry` >>
     simp[run_context_def, passSimulationDefsTheory.terminates_def] >>
     rename1 `lookup_function nm C.ctx_functions` >>
     Cases_on `lookup_function nm C.ctx_functions` >>
     simp[passSimulationDefsTheory.terminates_def] >>
     rename1 `run_function _ _ f0` >>
     Cases_on `fn_entry_label f0` >>
     simp[run_function_def, passSimulationDefsTheory.terminates_def]) >>
  `run_context fuel C vs =
   run_blocks fuel C fn
     (vs with <|vs_current_bb := lbl; vs_inst_idx := 0; vs_prev_bb := NONE|>)` by
    simp[run_context_def, run_function_def] >>
  qabbrev_tac `s =
    vs with <|vs_current_bb := lbl; vs_inst_idx := 0; vs_prev_bb := NONE|>` >>
  `!k G g. G.ctx_entry = SOME name /\ lookup_function name G.ctx_functions = SOME g /\
     fn_entry_label g = SOME lbl ==> run_context k G vs = run_blocks k G g s` by
    (rw[run_context_def, run_function_def, Abbr `s`] >> AP_TERM_TAC >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!e. run_blocks fuel C fn s <> Error e` by
    (rpt strip_tac >> qpat_x_assum `terminates _` mp_tac >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `finite_run C fn s (run_blocks fuel C fn s)` by
    metis_tac[cj 3 finite_execution_complete] >>
  drule finite_run_entry_active >> strip_tac >>
  qabbrev_tac `r = run_blocks fuel C fn s` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (fs[Abbr `q0`, Abbr `s`] >> metis_tac[joint_initial_entry]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule_all layout_stage_source_decoration >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `s.vs_allocas = FEMPTY` by simp[Abbr `s`] >>
  `?fn' positions.
     lookup_function name C'.ctx_functions = SOME fn' /\
     layout_driver_row C' fn fn' positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST path) (MAP SND path)
       ass qe q0 0 fn s fn' s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `activation_depth q0 = 0` by simp[Abbr `q0`, frameActivationCacheTheory.activation_depth_def] >>
  `layout_cut_safe D lo (SUC (LENGTH vs.vs_gas_readings)) vs C qe` by
    metis_tac[layout_cut_safe_whole_run] >>
  `?r'. run_blocks fuel C' fn' s = r' /\ finite_run C' fn' s r' /\
    layout_canonical_OutR D lo vs C C' q0 (MAP FST path) (MAP SND path)
      ass qe q0 0 qe (0 + LENGTH path) fn s fn' s r r' /\
    run_events_agree C C' fn s fn' s r r'` by
    (irule layout_stage_selected_run_fuel >> metis_tac[]) >>
  `!ret t. r <> IntRet ret t` by
    (drule o1_ctx_shape_no_intret >>
     disch_then (qspecl_then [`fuel`, `vs`] mp_tac) >>
     simp[run_context_def, run_function_def, Abbr `r`, Abbr `s`]) >>
  `dead_result_rel D r r'` by
    (fs[layout_canonical_OutR_def] >>
     Cases_on `r` >> Cases_on `r'` >> gvs[layout_canonical_result_def]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  `fn_entry_label fn' = SOME lbl` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     qspecl_then [`layout.cl_positions`, `fn`] mp_tac
       (GEN_ALL concretize_positions_entry_label) >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]) >>
  qabbrev_tac `n = fuel` >>
  `run_blocks n C' fn' s = r'` by simp[Abbr `n`] >>
  `!e. r' <> Error e` by metis_tac[cj 3 finite_execution_nonerror] >>
  `terminates r'` by
    (qpat_x_assum `!e. r' <> Error e` mp_tac >>
     Cases_on `r'` >> simp[passSimulationDefsTheory.terminates_def]) >>
  `run_context n C' vs = r'` by metis_tac[] >>
  `gas_events_blocks n C' fn' s = gas_events_blocks fuel C fn s` by
    (qunabbrev_tac `r` >>
     qpat_x_assum `run_events_agree _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [run_events_agree_def]) >>
     disch_then (qspecl_then [`fuel`, `n`] mp_tac) >> simp[]) >>
  `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> = s` by
    simp[Abbr `s`, venomStateTheory.venom_state_component_equality] >>
  qexistsl [`n`, `name`, `fn`, `fn'`, `lbl`] >>
  pop_assum (fn th => rewrite_tac[th]) >> simp[]
QED

Theorem layout_stage_terminating_context:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  terminates (run_context fuel C vs) ==>
  ?fuel'. dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs)
Proof
  strip_tac >> mp_tac layout_stage_terminating_events >>
  impl_tac >- metis_tac[] >> metis_tac[]
QED

(* The target entry function keeps the source's name and entry label. *)
Theorem layout_stage_target_entry[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  lookup_function name C.ctx_functions = SOME fn /\ fn.fn_eom = NONE ==>
  ?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> drule_all layout_stage_row_produce >> strip_tac >>
  qexists `out` >>
  gvs[layout_stage_row_def, apply_context_concretize_layout_def,
      apply_concretize_layout_def,
      venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
  qspecl_then [`layout.cl_positions`, `fn`] mp_tac
    (GEN_ALL concretize_positions_entry_label) >>
  simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]
QED

(* The source prefix of a pointer-safe entry run is a prefix of the
   target entry function's run. *)
Theorem layout_stage_prefix_simulation[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ dead_wf D /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  lookup_function name C'.ctx_functions = SOME fn' /\ fn_entry_label fn = SOME lbl /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  finite_run_prefix C fn s es /\ LENGTH es = n ==>
  finite_run_prefix C' fn' s es
Proof
  strip_tac >>
  qpat_x_assum `o1_ptr_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [o1_ptr_safe_upto_def]) >>
  `EVERY wf_function C.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  drule (cj 2 finite_prefix_entry) >> strip_tac >>
  rename1 `active_inst fn inst' p` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`] >> qpat_x_assum `s = _` SUBST_ALL_TAC >>
     irule joint_initial_entry >> metis_tac[]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule (cj 2 finite_prefix_decoration_complete) >>
  disch_then (qspecl_then [`q0`, `0`, `p`] mp_tac) >> simp[] >> strip_tac >>
  `joint_segment C q0 w qe` by metis_tac[cj 2 decorated_prefix_segment] >>
  drule_all layout_stage_segment_annotations >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `vs.vs_allocas = FEMPTY /\ s.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `?fn2 positions.
     lookup_function name C'.ctx_functions = SOME fn2 /\
     layout_driver_row C' fn fn2 positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST w) (MAP SND w)
       ass qe q0 0 fn s fn2 s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `fn2 = fn'` by fs[] >> qpat_x_assum `fn2 = fn'` SUBST_ALL_TAC >>
  `activation_depth q0 = 0` by
    simp[Abbr `q0`, frameActivationCacheTheory.activation_depth_def] >>
  drule (cj 2 decorated_prefix_end) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fe`, `ie`, `se`] strip_assume_tac)) >>
  `n <> 0` by (strip_tac >> fs[LENGTH_NIL]) >>
  `joint_state qe = se` by
    (Cases_on `qe` >> fs[decoration_at_def, joint_state_def]) >>
  `gas_cut n vs (joint_state qe)` by fs[gas_cut_def, LENGTH_DROP] >>
  `layout_cut_safe D lo n vs C qe` by fs[layout_cut_safe_def] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    metis_tac[o1_ctx_shape_instructions_wf] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
  `selected_simulation_contract_fuel C C' q0 w
    (layout_canonical_ES D lo vs C C' q0 w (MAP FST w) (MAP SND w) ass qe)
    (layout_canonical_EB D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe)
    (layout_canonical_run D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe)
    (events_OS C C' (layout_deferred_OS D lo vs C C' q0 w (MAP FST w) (MAP SND w) ass qe))
    (events_OB C C' (layout_canonical_OB D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe))
    (events_OutR C C' (layout_canonical_OutR D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe))` by
    (irule layout_canonical_simulation_contract_fuel >> metis_tac[]) >>
  `selected_prefix_certificates C C' q0 w
    (layout_canonical_ES D lo vs C C' q0 w (MAP FST w) (MAP SND w) ass qe)
    (layout_canonical_EB D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe)
    (layout_canonical_run D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe)
    (events_OS C C' (layout_deferred_OS D lo vs C C' q0 w (MAP FST w) (MAP SND w) ass qe))
    (events_OB C C' (layout_canonical_OB D lo vs C C' q0 (MAP FST w) (MAP SND w) ass qe))` by
    (irule layout_canonical_prefix_certificates >> metis_tac[]) >>
  qpat_x_assum `s = _` SUBST_ALL_TAC >>
  drule_all selected_prefix_simulation >> fs[]
QED

(* Root entry, prefix form: the target run has the source's first n GAS
   events whenever the source has n and is pointer-safe up to its n-th
   gas reading, whether or not it terminates. *)
Theorem layout_stage_prefix_events:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ dead_wf D /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  n <= LENGTH (gas_events_blocks fuel C fn s) ==>
  ?fuel' fn'. C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel' C' fn' s) /\
    TAKE n (gas_events_blocks fuel' C' fn' s) = TAKE n (gas_events_blocks fuel C fn s)
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `EVERY wf_function C.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM, o1_ptr_safe_upto_def] >>
  `?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
     fn_entry_label fn' = SOME lbl` by metis_tac[layout_stage_target_entry] >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  Cases_on `n = 0` >- (qexistsl [`0`, `fn'`] >> gvs[]) >>
  qabbrev_tac `es0 = TAKE n (gas_events_blocks fuel C fn s)` >>
  `LENGTH es0 = n` by simp[Abbr `es0`, LENGTH_TAKE] >>
  `?k. !k'. k <= k' ==> ?rest. gas_events_blocks k' C' fn' s = es0 ++ rest`
    suffices_by
    (strip_tac >> qexistsl [`k`, `fn'`] >>
     first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
     gvs[TAKE_LENGTH_APPEND]) >>
  irule finite_run_prefix_realizable >>
  `finite_run_prefix C fn s es0` by
    (simp[Abbr `es0`] >> irule gas_events_blocks_prefix >> gvs[]) >>
  irule layout_stage_prefix_simulation >> metis_tac[]
QED

Theorem layout_stage_terminating_context_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  terminates (run_context fuel C vs) ==>
  dead_result_rel D (run_context fuel C vs) (run_context fuel C' vs)
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  Cases_on `C.ctx_entry` >>
  gvs[run_context_def, passSimulationDefsTheory.terminates_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >>
  gvs[passSimulationDefsTheory.terminates_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >>
  gvs[run_function_def, passSimulationDefsTheory.terminates_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qmatch_goalsub_abbrev_tac `run_blocks fuel C fn s` >>
  `finite_run C fn s (run_blocks fuel C fn s)` by
    (irule (cj 3 finite_execution_complete) >>
     Cases_on `run_blocks fuel C fn s` >> gvs[]) >>
  drule finite_run_entry_active >> strip_tac >>
  qmatch_goalsub_abbrev_tac `dead_result_rel D r _` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`, Abbr `s`] >> metis_tac[joint_initial_entry]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule_all layout_stage_source_decoration >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `s.vs_allocas = FEMPTY` by simp[Abbr `s`] >>
  `?fn' positions.
     lookup_function name C'.ctx_functions = SOME fn' /\
     layout_driver_row C' fn fn' positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST path) (MAP SND path)
       ass qe q0 0 fn s fn' s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `activation_depth q0 = 0` by simp[Abbr `q0`, frameActivationCacheTheory.activation_depth_def] >>
  `layout_cut_safe D lo (SUC (LENGTH vs.vs_gas_readings)) vs C qe` by
    metis_tac[layout_cut_safe_whole_run] >>
  `?r'. run_blocks fuel C' fn' s = r' /\ finite_run C' fn' s r' /\
    layout_canonical_OutR D lo vs C C' q0 (MAP FST path) (MAP SND path)
      ass qe q0 0 qe (0 + LENGTH path) fn s fn' s r r' /\
    run_events_agree C C' fn s fn' s r r'` by
    (qunabbrev_tac `r` >> irule layout_stage_selected_run_fuel >> metis_tac[]) >>
  `!ret t. r <> IntRet ret t` by
    (drule o1_ctx_shape_no_intret >>
     disch_then (qspecl_then [`fuel`, `vs`] mp_tac) >>
     simp[run_context_def, run_function_def, Abbr `r`, Abbr `s`]) >>
  `dead_result_rel D r r'` by
    (fs[layout_canonical_OutR_def] >>
     Cases_on `r` >> Cases_on `r'` >> gvs[layout_canonical_result_def]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  `fn_entry_label fn' = SOME lbl` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     qspecl_then [`layout.cl_positions`, `fn`] mp_tac
       (GEN_ALL concretize_positions_entry_label) >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]) >>
  simp[Abbr `s`]
QED

Theorem layout_stage_context_revert_empty:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  run_context fuel C vs = Abort Revert_abort post /\ post.vs_returndata = [] /\
  run_context fuel C' vs = Abort Revert_abort tpost ==>
  tpost.vs_returndata = []
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  Cases_on `C.ctx_entry` >> gvs[run_context_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> gvs[run_function_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qpat_x_assum `run_blocks fuel C fn _ = _`
    (fn th => assume_tac th) >>
  qmatch_asmsub_abbrev_tac `run_blocks fuel C fn s` >>
  `finite_run C fn s (run_blocks fuel C fn s)` by
    (irule (cj 3 finite_execution_complete) >> simp[]) >>
  drule finite_run_entry_active >> strip_tac >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`, Abbr `s`] >> metis_tac[joint_initial_entry]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule_all layout_stage_source_decoration >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `s.vs_allocas = FEMPTY` by simp[Abbr `s`] >>
  `?fn' positions.
     lookup_function name C'.ctx_functions = SOME fn' /\
     layout_driver_row C' fn fn' positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST path) (MAP SND path)
       ass qe q0 0 fn s fn' s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `activation_depth q0 = 0` by simp[Abbr `q0`, frameActivationCacheTheory.activation_depth_def] >>
  `?r'. run_blocks fuel C' fn' s = r' /\ finite_run C' fn' s r' /\
    layout_canonical_OutR D lo vs C C' q0 (MAP FST path) (MAP SND path)
      ass qe q0 0 qe (0+LENGTH path) fn s fn' s (run_blocks fuel C fn s) r' /\
    (!a b. run_blocks fuel C fn s = Abort Revert_abort a /\
      r' = Abort Revert_abort b /\ a.vs_returndata = [] ==> b.vs_returndata = [])` by
    (irule layout_stage_selected_run_fuel_revert_empty >> simp[] >>
     rpt conj_tac
     >- (qexists `P` >> simp[])
     >- (qexists `names` >> simp[])
     >- (qexists `rpolicy` >> simp[])
     >- (qexists `path` >> gvs[])
     >> qexists `d` >> gvs[]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  `fn_entry_label fn' = SOME lbl` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     qspecl_then [`layout.cl_positions`, `fn`] mp_tac
       (GEN_ALL concretize_positions_entry_label) >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]) >>
  gvs[run_function_def, Abbr `s`] >> metis_tac[]
QED

val _ = export_theory();
