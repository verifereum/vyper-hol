Theory concretizePtrDallocaRuntimeHistory
Ancestors
  concretizePtrDallocaHistoricalRead concretizePtrDallocaHistoricalPersistent
  concretizePtrDallocaEndpointDemands concretizePtrDallocaActualWrites
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrLifetime concretizePtrOpaqueRetpc
  concretizePtrSourceOwnership concretizePtrDallocaGhostInterface
  concretizePtrParamSupport concretizePtrParamShape
  concretizePtrLedgerAlignment concretizePtrPairedFields
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrSharedFields
  concretizePtrPrefixLedger concretizeStepStructure o1PassContract venomWf
  lowerDloadPtrDalloca concretizePtrObservationInterface
  venomExecSemantics venomInstProofs opcodeClass
  concretizeMemLocDefs passSharedDefs ptrDiscipline venomState venomInst
  list finite_map pred_set words

Theorem ptr_dalloca_historical_output_mask:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ n0 = EL q done /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n0 h).po_taint op) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans ==>
  out_taint (EL q ht).po_taint (EL q ht).po_inst (EL q ht).po_state SUBSET
    out_taint (EL n0 h).po_taint (EL n0 h).po_inst (EL n0 h).po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  mp_tac (Q.INST [`a` |-> `EL n0 h`, `t` |-> `EL q ht`]
    ptr_dalloca_actual_event_context) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej)` >>
  `EL n0 H = (tsj,rj,bj,PTj,TGj,sj,ej)` by simp[] >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  Cases_on `(EL n0 h).po_inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _` mp_tac >>
      simp[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
      rpt strip_tac >> gvs[mk_assign_inst_def, mk_nop_inst_def,
                           out_taint_def, op_taint_def, eval_operand_def] >>
      rpt CASE_TAC >> simp[]) >>
  `(EL q ht).po_inst = (EL n0 h).po_inst` by
    gvs[concretize_inst_with_positions_def] >>
  Cases_on `MEM (EL n0 h).po_inst.inst_opcode [ILOAD;SLOAD;TLOAD]`
  >- (drule_all ptr_dalloca_historical_scalar_read_masks >> simp[]) >>
  Cases_on `(EL n0 h).po_inst.inst_opcode = MLOAD`
  >- (drule_all ptr_dalloca_historical_mload_read_mask >> strip_tac >>
      gvs[out_taint_def]) >>
  mp_tac (Q.INST [`a` |-> `EL n0 h`, `t` |-> `EL q ht`]
    ptr_dalloca_historical_persistent_context) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!a wt. eval_operand a (EL q ht).po_state = SOME wt ==>
    ?w. eval_operand a (EL n0 h).po_state = SOME w` by
    (rpt strip_tac >> drule_all ptr_mixed_vars_eval_presence >>
     disch_then (qspec_then `a` mp_tac) >>
     Cases_on `eval_operand a (EL n0 h).po_state` >> fs[]) >>
  qpat_assum `(EL q ht).po_inst = (EL n0 h).po_inst`
    (fn th => rewrite_tac[th]) >>
  mp_tac (Q.INST [`P` |-> `P'`, `TG` |-> `TGj'`,
    `births` |-> `bj'`, `positions` |-> `positions`,
    `fn` |-> `(EL n0 h).po_fn`, `ft` |-> `(EL q ht).po_fn`,
    `tn` |-> `(EL n0 h).po_taint`, `tnt` |-> `(EL q ht).po_taint`,
    `s` |-> `(EL n0 h).po_state`, `t` |-> `(EL q ht).po_state`,
    `inst` |-> `(EL n0 h).po_inst`]
    (INST_TYPE [alpha |-> ``:num``] ptr_dalloca_runtime_mask_demands)) >>
  (impl_tac >- (fs[MEM] >> metis_tac[])) >> simp[]
QED

(* The two raw executions below are obtained from the actual adjacent
   observations. Runtime provenance uses the raw poststate, before the
   chronology advances its instruction cursor. *)
Theorem ptr_dalloca_runtime_chrono_next:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  ptr_chrono_step Ct at bt /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  ((a.po_inst.inst_opcode = ALLOCA /\ at.po_inst.inst_opcode = ASSIGN /\
      (?pos. at.po_inst.inst_operands = [Lit pos]) /\
      at.po_inst.inst_outputs = a.po_inst.inst_outputs) \/
   (a.po_inst.inst_opcode <> ALLOCA /\ at.po_inst = a.po_inst)) /\
  fn_ptr_ok P a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  FDOM a.po_prov SUBSET fn_pv P a.po_fn /\
  ((a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
     ?x y. a.po_inst.inst_operands = [x;y]) /\
  (a.po_inst.inst_opcode = ASSIGN ==> ?op. a.po_inst.inst_operands = [op]) /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
     FLOOKUP at.po_prov v = SOME site) /\
  ptr_ledger_erases dyn births TG a.po_prov /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels /\
  ((a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
     !op. MEM op a.po_inst.inst_operands ==>
       ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {}) /\
  LENGTH PT = LENGTH a.po_params /\ LENGTH a.po_params = LENGTH at.po_params /\
  (!k site. k < LENGTH a.po_params /\ EL k at.po_params = SOME site ==>
     EL k a.po_params = SOME site /\ EL k PT = NONE) /\
  (!k site. k < LENGTH a.po_params /\ EL k PT = NONE /\
     EL k a.po_params = SOME site ==> EL k at.po_params = SOME site) /\
  (!k site. k < LENGTH at.po_params /\ EL k at.po_params = SOME site ==>
     EL k a.po_state.vs_params = EL k at.po_state.vs_params) /\
  a.po_state.vs_fmp = at.po_state.vs_fmp /\
  (a.po_inst.inst_opcode = DALLOCA ==>
     eval_operands a.po_inst.inst_operands a.po_state =
       eval_operands a.po_inst.inst_operands at.po_state) /\
  (a.po_inst.inst_opcode <> ALLOCA ==>
     out_taint at.po_taint a.po_inst at.po_state SUBSET
       out_taint a.po_taint a.po_inst a.po_state) ==>
  (ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TG' v = NONE) /\
  (!v site. FLOOKUP TG' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site)) /\
  PT' = PT /\ saved' = saved /\
  b.po_params = a.po_params /\ bt.po_params = at.po_params /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  b.po_state.vs_params = a.po_state.vs_params /\
  bt.po_state.vs_params = at.po_state.vs_params
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_terminator at.po_inst.inst_opcode /\ at.po_inst.inst_opcode <> INVOKE` by
    (Cases_on `a.po_inst.inst_opcode = ALLOCA` >> fs[is_terminator_def]) >>
  pop_assum strip_assume_tac >>
  `!sfuel source_post tfuel target_post.
    step_inst sfuel C a.po_inst a.po_state = OK source_post /\
    step_inst tfuel Ct at.po_inst at.po_state = OK target_post ==>
    ptr_dalloca_ghost_vars
      (step_prov a.po_params a.po_prov a.po_inst source_post)
      (step_taint a.po_inst a.po_state source_post a.po_taint).t_var
      (source_post with vs_inst_idx := SUC a.po_state.vs_inst_idx)
      (step_prov at.po_params at.po_prov at.po_inst target_post)
      (step_taint at.po_inst at.po_state target_post at.po_taint).t_var
      (target_post with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    (!v site.
      FLOOKUP (step_prov at.po_params at.po_prov at.po_inst target_post) v = SOME site ==>
      FLOOKUP (ptr_tagged_step token PT TG a.po_inst source_post) v = NONE) /\
    (!v site.
      FLOOKUP (ptr_tagged_step token PT TG a.po_inst source_post) v = NONE /\
      FLOOKUP (step_prov a.po_params a.po_prov a.po_inst source_post) v = SOME site ==>
      FLOOKUP (step_prov at.po_params at.po_prov at.po_inst target_post) v = SOME site)` by
    (map_every qx_gen_tac [`sfuel`,`source_post`,`tfuel`,`target_raw_state`] >> strip_tac >>
     mp_tac (Q.INST [
       `inst` |-> `a.po_inst`, `instt` |-> `at.po_inst`,
       `fn` |-> `a.po_fn`, `f` |-> `a.po_fn`, `g` |-> `at.po_fn`,
       `G` |-> `a.po_prov`, `Gout` |-> `at.po_prov`,
       `tn` |-> `a.po_taint`, `tnt` |-> `at.po_taint`,
       `s` |-> `a.po_state`, `t` |-> `at.po_state`,
       `PG` |-> `a.po_params`, `PGout` |-> `at.po_params`,
       `fuel` |-> `sfuel`, `fuelt` |-> `tfuel`,
       `s'` |-> `source_post`, `t'` |-> `target_raw_state`]
       ptr_dalloca_runtime_next_mask) >>
     (impl_tac >- (fs[] >> metis_tac[])) >> simp[]) >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >>
    disch_then (mp_tac o MATCH_MP step_inst_base_intret_opcodes) >>
    strip_tac >> gvs[is_terminator_def]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >>
    disch_then (mp_tac o MATCH_MP step_inst_base_intret_opcodes) >>
    strip_tac >> gvs[is_terminator_def]) >>
  qpat_x_assum `!sfuel source_post tfuel target_post. _`
    (drule_all_then mp_tac) >>
  imp_res_tac step_preserves_params >> simp[]
QED

(* Assemble every local runtime premise at the actual matched departure. *)
Theorem ptr_dalloca_historical_runtime_next:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ n0 = EL q done /\ a = EL n0 h /\ t = EL q ht /\
  EL n0 H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_tagged_chrono_step C token a (EL (SUC n0) h)
    PTj TGj sj PTnext TGnext savednext /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY bj
    (\token aid. F) a t /\
  (!v site. FLOOKUP t.po_prov v = SOME site ==> FLOOKUP TGj v = NONE) /\
  (!v site. FLOOKUP TGj v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
     FLOOKUP t.po_prov v = SOME site) /\
  LENGTH PTj = LENGTH a.po_params /\ LENGTH a.po_params = LENGTH t.po_params /\
  (!k site. k < LENGTH a.po_params ==>
    (EL k t.po_params = SOME site ==>
      EL k a.po_params = SOME site /\ EL k PTj = NONE /\
      EL k a.po_state.vs_params = EL k t.po_state.vs_params) /\
    (EL k PTj = NONE /\ EL k a.po_params = SOME site ==>
      EL k t.po_params = SOME site)) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r i. j < n0 /\ r < LENGTH done /\ EL r done = j /\ i < lo ==>
    i IN (EL r ht).po_taint.t_mem ==> i IN (EL j h).po_taint.t_mem) /\
  (!j r i. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= i ==>
    i IN (EL r ht).po_taint.t_mem ==> i IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  (ptr_dalloca_ghost_vars
    (EL (SUC n0) h).po_prov (EL (SUC n0) h).po_taint.t_var (EL (SUC n0) h).po_state
    (EL (SUC q) ht).po_prov (EL (SUC q) ht).po_taint.t_var (EL (SUC q) ht).po_state /\
   (!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==>
     FLOOKUP TGnext v = NONE) /\
   (!v site. FLOOKUP TGnext v = NONE /\
     FLOOKUP (EL (SUC n0) h).po_prov v = SOME site ==>
     FLOOKUP (EL (SUC q) ht).po_prov v = SOME site)) /\
  PTnext = PTj /\ savednext = sj /\
  (EL (SUC n0) h).po_params = a.po_params /\
  (EL (SUC q) ht).po_params = t.po_params /\
  (EL (SUC n0) h).po_stack = a.po_stack /\
  (EL (SUC q) ht).po_stack = t.po_stack /\
  (EL (SUC n0) h).po_state.vs_params = a.po_state.vs_params /\
  (EL (SUC q) ht).po_state.vs_params = t.po_state.vs_params

Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ptr_dalloca_ghost_sample _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def]) >>
  `!op. op_taint t.po_taint op SUBSET op_taint a.po_taint op` by
    (gen_tac >> Cases_on `op` >>
     fs[op_taint_def, ptr_dalloca_ghost_vars_def, entry_taint_def] >> metis_tac[]) >>
  `!i. i < lo ==> i IN t.po_taint.t_mem ==> i IN a.po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. (i < lo \/ _) /\ _ ==> _` irule >> simp[]) >>
  `!i. dyn_floor C vs <= i ==>
       i IN t.po_taint.t_mem ==> i IN a.po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. (i < lo \/ _) /\ _ ==> _` irule >> simp[]) >>
  `out_taint t.po_taint t.po_inst t.po_state SUBSET
     out_taint a.po_taint a.po_inst a.po_state` by
    (mp_tac (Q.INST [`n0` |-> `n0`, `q` |-> `q`]
      ptr_dalloca_historical_output_mask) >>
     (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]) >>
  mp_tac (Q.INST [`a` |-> `a`, `t` |-> `t`]
    ptr_dalloca_actual_event_context) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `EL (EL q done) H =
    (tsEvent,rEvent,bEvent,ptEvent,tgEvent,sEvent,eEvent)` >>
  `tsEvent = tsj /\ rEvent = rj /\ bEvent = bj /\ ptEvent = PTj /\
   tgEvent = TGj /\ sEvent = sj /\ eEvent = ej` by gvs[] >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`tsEvent = tsj`, `rEvent = rj`, `bEvent = bj`, `ptEvent = PTj`,
     `tgEvent = TGj`, `sEvent = sj`, `eEvent = ej`] >>
  `?P0. EVERY (fn_ptr_ok P0) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by fs[ptr_observation_reachable_def] >>
  mp_tac (Q.INST [`P` |-> `P0`, `fn` |-> `a.po_fn`,
    `G` |-> `a.po_prov`, `PG` |-> `a.po_params`, `tn` |-> `a.po_taint`,
    `s` |-> `a.po_state`, `inst` |-> `a.po_inst`, `stk` |-> `a.po_stack`,
    `vs0` |-> `vs`, `ctx` |-> `C`] ptr_frame_current_static) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `fn_ptr_ok P0 a.po_fn /\ inst_wf a.po_inst` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `FDOM a.po_prov SUBSET fn_pv P0 a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `((a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
      ?x y. a.po_inst.inst_operands = [x;y]) /\
   (a.po_inst.inst_opcode = ASSIGN ==>
      ?op. a.po_inst.inst_operands = [op])` by
    (conj_tac >> strip_tac >>
     qpat_x_assum `inst_wf a.po_inst` mp_tac >>
     fs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `((a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
     !op. MEM op a.po_inst.inst_operands ==>
       ptr_nonopaque_operand a.po_fn op /\ op_taint a.po_taint op = {})` by
    (strip_tac >>
     `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     (conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
      qpat_x_assum `taint_ok a.po_fn a.po_taint a.po_inst a.po_state`
        (mp_tac o Q.SPEC `op` o CONJUNCT1 o REWRITE_RULE [taint_ok_def]) >>
      simp[])) >>
  `ptr_ledger_erases (dyn_floor C vs) bj TGj a.po_prov` by
    (drule_all ptr_source_ownership_prov_erases >> simp[]) >>
  mp_tac (Q.INST [`q` |-> `q`, `a` |-> `a`, `t` |-> `t`]
    ptr_dalloca_historical_sample) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `ptr_history_content a.po_taint a.po_state t.po_state` by
    gvs[ptr_paired_sample_def] >>
  `a.po_state.vs_fmp = t.po_state.vs_fmp` by
    (drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  `(a.po_inst.inst_opcode = DALLOCA ==>
    eval_operands a.po_inst.inst_operands a.po_state =
      eval_operands a.po_inst.inst_operands t.po_state)` by
    (strip_tac >>
     `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> simp[]) >>
     `!op. MEM op a.po_inst.inst_operands ==>
       eval_operand op a.po_state = eval_operand op t.po_state` by
       (rpt strip_tac >>
        `op_prov a.po_prov op = NONE /\ op_taint a.po_taint op = {}` by
          (drule_all dalloca_operand_clean >> simp[]) >>
        irule (Q.INST [`dyn` |-> `dyn_floor C vs`, `births` |-> `bj`,
          `positions` |-> `positions`, `TG` |-> `TGj`, `G` |-> `a.po_prov`,
          `tn` |-> `a.po_taint`, `f` |-> `a.po_fn`, `g` |-> `(EL q ht).po_fn`]
          ptr_mixed_scalar_eval) >>
        simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
     `?sizeop. a.po_inst.inst_operands = [sizeop]` by
       fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     qpat_x_assum `!op. MEM op a.po_inst.inst_operands ==> _`
       (qspec_then `sizeop` mp_tac) >>
     simp[eval_operands_def]) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `ptr_paired_cursor lp a t` by
    (mp_tac (Q.SPEC `ws` (Q.INST [`j` |-> `q`, `a` |-> `endpoint`,
       `local_positions` |-> `lp`, `vs0` |-> `vs`, `Ct` |-> `C'`]
       ptr_paired_prefix_alignment)) >>
     (impl_tac >- gvs[]) >> simp[EL_APPEND_EQN]) >>
  `t.po_inst.inst_opcode <> NOP` by
    (qpat_x_assum `ptr_paired_cursor lp a t` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `t.po_state.vs_inst_idx` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `((a.po_inst.inst_opcode = ALLOCA /\ t.po_inst.inst_opcode = ASSIGN /\
      (?pos. t.po_inst.inst_operands = [Lit pos]) /\
      t.po_inst.inst_outputs = a.po_inst.inst_outputs) \/
    (a.po_inst.inst_opcode <> ALLOCA /\ t.po_inst = a.po_inst))` by
    (Cases_on `a.po_inst.inst_opcode = ALLOCA`
     >- (`?out. a.po_inst.inst_outputs = [out]` by
           fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
         qpat_x_assum `t.po_inst = concretize_inst_with_positions _ _` mp_tac >>
         simp[concretize_inst_with_positions_def] >>
         CASE_TAC >> strip_tac >>
         gvs[mk_assign_inst_def, mk_nop_inst_def]) >>
     gvs[concretize_positions_unchanged]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_chrono_step C' t (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  mp_tac (Q.INST [
    `C` |-> `C`, `Ct` |-> `C'`, `token` |-> `token`,
    `a` |-> `a`, `b` |-> `EL (SUC n0) h`,
    `at` |-> `t`, `bt` |-> `EL (SUC q) ht`,
    `P` |-> `P0`, `dyn` |-> `dyn_floor C vs`, `births` |-> `bj`,
    `PT` |-> `PTj`, `TG` |-> `TGj`, `saved` |-> `sj`,
    `PT'` |-> `PTnext`, `TG'` |-> `TGnext`, `saved'` |-> `savednext`]
    ptr_dalloca_runtime_chrono_next) >>
  (impl_tac >- (simp[] >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED
