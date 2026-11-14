Theory concretizePtrDallocaRuntimeHistory
Ancestors
  concretizePtrDallocaHistoricalRead concretizePtrDallocaHistoricalPersistent
  concretizePtrDallocaEndpointDemands concretizePtrDallocaActualWrites
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrLifetime concretizePtrOpaqueRetpc
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
