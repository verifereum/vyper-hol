Theory concretizePtrDallocaFrameEndpoint
Ancestors
  concretizePtrDallocaGhostHistory concretizePtrDallocaEndpointDemands
  concretizePtrDallocaDisciplineTransport concretizePtrCurrentRangeTransport
  concretizePtrObservationInterface concretizePtrMloadEndpoint concretizePtrReadOrigin
  concretizePtrStagePlacements concretizePtrStageBounds concretizePtrOwnerFloor
  concretizePtrOwnerPath
  concretizePtrParamShape concretizePtrParamSupport concretizePtrTaggedSupport
  concretizePtrForwardingTransport concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding
  concretizePtrDallocaGhostInterface concretizePtrSourceOwnership
  concretizePtrOwnershipErasure concretizePtrPrefixLedger concretizePtrPairedFields
  concretizeStepStructure concretizeMemLocDefs memLocDefs ptrDiscipline
  o1PassContract unitShapeDefs unitTransformDefs unitMemInv venomExecProofs frameAllocationOwnership
  passSharedDefs
  memSafeRun venomWf venomInst venomState contextCodegenRel codegenRel
  list rich_list arithmetic words finite_map pred_set

(* The runtime frame contract is consumed at the actual final paired sample. *)
Theorem ptr_dalloca_paired_frame_ptr_static:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp)` by simp[] >>
  `eom < dimword(:256)` by metis_tac[w2n_lt, LESS_EQ_LESS_TRANS] >>
  `lo <= eom` by (drule_all ptr_stage_fixed_region_bound >> simp[]) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_prefix_samples >>
  disch_then (strip_assume_tac o
    REWRITE_RULE[ptr_paired_samples_def, ptr_sample_list_def]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `ptr_observation_reachable vs C a` by
    (qpat_assum `ptr_chrono_history vs C h a`
       (mp_tac o MATCH_MP ptr_chrono_history_reachable) >> simp[]) >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by fs[ptr_observation_reachable_def] >>
  `MEM a.po_fn C.ctx_functions` by
    (drule frame_reachable_functions_member >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_owner_frame_active >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `EVERY wf_function C.ctx_functions /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst /\ wf_function a.po_fn /\
   fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn /\ label_positions_ok a.po_inst` by
    (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (qpat_assum `at.po_inst = concretize_inst_with_positions _ _` mp_tac >>
      `LENGTH a.po_inst.inst_outputs = 1` by fs[inst_wf_def] >>
      fs[LENGTH_EQ_NUM_compute] >>
      Cases_on `FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id)` >>
      simp[concretize_inst_with_positions_def, AllCaseEqs()] >>
      rpt strip_tac >>
      fs[mk_assign_inst_def, mk_nop_inst_def, access_ok_def, taint_ok_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         op_taint_def]) >>
  `at.po_inst = a.po_inst` by
    simp[concretize_positions_unchanged] >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by metis_tac[] >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> drule_all ptr_source_tagged_var_support >> simp[]) >>
  qpat_assum `ptr_paired_sample positions a at
    (tokens,registry,births,PT,TG,saved,entries)`
    (strip_assume_tac o REWRITE_RULE[ptr_paired_sample_def]) >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels] >>
  `h <> [] /\ LAST h = a` by
    (qpat_assum `ptr_chrono_history vs C h a`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >> simp[]) >>
  `ht <> [] /\ LAST ht = at` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >> simp[]) >>
  `H <> []` by (strip_tac >> gvs[]) >>
  `LENGTH h-1 < LENGTH h /\ LENGTH ht-1 = LENGTH done /\
   LENGTH H-1 = LENGTH h-1` by decide_tac >>
  `EL (LENGTH done) ht = at /\ EL (LENGTH h-1) h = a /\
   EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (qpat_x_assum `LAST ht = at` mp_tac >>
     qpat_x_assum `LAST h = a` mp_tac >>
     qpat_x_assum `LAST H = (tokens,registry,births,PT,TG,saved,entries)` mp_tac >>
     simp[LAST_EL, PRE_SUB1]) >>
  Q.SUBGOAL_THEN
    `LENGTH done = 0 \/ EL (LENGTH done-1) done < LENGTH h-1` ASSUME_TAC
  >- (Cases_on `LENGTH done = 0` >- fs[] >>
     `LENGTH done-1 < LENGTH done` by decide_tac >>
     qpat_assum `ptr_event_embedding h ht (done ++ [LENGTH h-1])`
       (mp_tac o List.last o CONJUNCTS o
          REWRITE_RULE[ptr_event_embedding_def]) >>
     disch_then (qspecl_then [`LENGTH done-1`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `LENGTH h-1 <= EL (LENGTH done) (done ++ [LENGTH h-1])` by
    simp[EL_APPEND_EQN] >>
  mp_tac (Q.INST [`endpoint` |-> `a`] ptr_dalloca_ghost_history_static) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`LENGTH h-1`,`LENGTH done`] mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then [`tokens`,`registry`,`births`,`PT`,`TG`,`saved`,`entries`]
    mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL (LENGTH h-1) h = a` (fn source_end =>
    qpat_assum `EL (LENGTH done) ht = at` (fn target_end =>
      disch_then (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE[source_end,target_end]))) >>
  qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY births
    (\token aid. F) a at`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def]) >>
  `!op. op_taint at.po_taint op SUBSET op_taint a.po_taint op` by
    (gen_tac >> Cases_on `op` >>
     fs[ptr_dalloca_ghost_vars_def, op_taint_def, entry_taint_def] >>
     metis_tac[]) >>
  Cases_on `in_revert_forward a.po_fn a.po_state`
  >- (`in_revert_forward at.po_fn at.po_state` by
        (drule_all ptr_paired_prefix_forwarding_static >> simp[]) >>
      `a.po_inst.inst_opcode = RETURNDATACOPY \/
       a.po_inst.inst_opcode = REVERT` by
        (qpat_assum `in_revert_forward a.po_fn a.po_state`
           (qx_choose_then `forwarding_bb` strip_assume_tac o
             REWRITE_RULE[in_revert_forward_def]) >>
         `get_instruction forwarding_bb a.po_state.vs_inst_idx = SOME a.po_inst` by
           (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
              (qx_choose_then `active_bb` strip_assume_tac o
                REWRITE_RULE[active_inst_def]) >>
            `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME active_bb` by
              (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
            gvs[get_instruction_def]) >>
         drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint a.po_taint op = {}` by
        (fs[taint_ok_def] >> metis_tac[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
        metis_tac[SUBSET_EMPTY] >>
      fs[access_ok_def, taint_ok_def, about_to_revert_def,
         source_memory_read_ranges_def] >> metis_tac[]) >>
  suspend "ordinary"
QED

Resume ptr_dalloca_paired_frame_ptr_static[ordinary]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_memory_prefix_def] >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `!v b sz. FLOOKUP at.po_prov v = SOME (b,sz) ==> dyn_floor C vs <= b` by
    (rpt strip_tac >>
     `FLOOKUP TG v = NONE` by metis_tac[] >>
     `FLOOKUP a.po_prov v = SOME (b,sz)` by
       (qpat_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE[ptr_dalloca_ghost_vars_def]) >>
        metis_tac[]) >>
     qpat_assum `ptr_ledger_erases _ _ _ _`
       (mp_tac o Q.SPEC `v` o CONJUNCT1 o
         REWRITE_RULE[ptr_ledger_erases_def]) >>
     simp[ptr_owner_erases_def]) >>
  `!v b sz. FLOOKUP a.po_prov v = SOME (b,sz) /\
     dyn_floor C vs <= b /\ 0 < sz ==> FLOOKUP at.po_prov v = SOME (b,sz)` by
    (rpt strip_tac >> Cases_on `FLOOKUP TG v`
     >- metis_tac[] >>
     rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
     drule_all ptr_stage_placements_live_owner_static >> strip_tac >>
     `b+sz <= dyn_floor C vs` by
       (drule_all ptr_reachable_owner_below_dyn_floor >> simp[]) >>
     qpat_assum `dyn_floor C vs <= b` mp_tac >>
     qpat_assum `0 < sz` mp_tac >>
     qpat_assum `b+sz <= dyn_floor C vs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qsuff_tac `F` >- simp[] >> decide_tac) >>
  `!ops token aid b sz p.
     (mem_read_ops a.po_inst = SOME ops \/ mem_write_ops a.po_inst = SOME ops) /\
     op_prov TG ops.iao_ofst = SOME (token,aid) /\
     FLOOKUP births (token,aid) = SOME (b,sz) /\
     FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
     p+sz <= eom /\ p+sz < dimword(:256)` by
    (rpt strip_tac >>
     `p+sz <= eom` by (drule_all ptr_stage_placements_endpoint_bound >> simp[]) >>
     decide_tac) >>
  mp_tac (Q.INST [`fn` |-> `a.po_fn`, `ft` |-> `at.po_fn`,
    `inst` |-> `a.po_inst`, `G` |-> `a.po_prov`, `Gout` |-> `at.po_prov`,
    `tn` |-> `a.po_taint`, `tnt` |-> `at.po_taint`,
    `s` |-> `a.po_state`, `t` |-> `at.po_state`, `dyn` |-> `dyn_floor C vs`]
    ptr_dalloca_access_cases) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >> strip_tac >>
  `access_ok eom at.po_prov at.po_fn a.po_inst at.po_state` by
    (mp_tac (Q.INST [`fn` |-> `a.po_fn`, `ft` |-> `at.po_fn`,
      `inst` |-> `a.po_inst`, `G` |-> `a.po_prov`, `Gout` |-> `at.po_prov`,
      `tn` |-> `a.po_taint`, `tnt` |-> `at.po_taint`,
      `s` |-> `a.po_state`, `t` |-> `at.po_state`, `dyn` |-> `dyn_floor C vs`]
      ptr_dalloca_access_transport_positive) >>
     (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `at.po_inst = a.po_inst` (fn th => rewrite_tac[th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `a.po_inst.inst_opcode = RETURNDATACOPY \/ a.po_inst.inst_opcode = REVERT`
  >- (`!op. MEM op a.po_inst.inst_operands ==> op_taint a.po_taint op = {}` by
        (qpat_assum `taint_ok a.po_fn a.po_taint a.po_inst a.po_state`
           (mp_tac o CONJUNCT1 o REWRITE_RULE[taint_ok_def]) >>
         qpat_assum `a.po_inst.inst_opcode = RETURNDATACOPY \/
           a.po_inst.inst_opcode = REVERT` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         qpat_x_assum `!operand. _` (qspec_then `op` mp_tac) >>
         qpat_x_assum `a.po_inst.inst_opcode = _` SUBST1_TAC >> simp[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
        metis_tac[SUBSET_EMPTY] >>
      fs[taint_ok_def, about_to_revert_def, source_memory_read_ranges_def] >>
      metis_tac[]) >>
  suspend "read_byte"
QED

Resume ptr_dalloca_paired_frame_ptr_static[read_byte]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `!off len i.
     MEM (off,len) (source_memory_read_ranges a.po_inst at.po_state) /\
     off <= i /\ i < off+len /\ i IN at.po_taint.t_mem ==>
     ?off_s j.
       MEM (off_s,len) (source_memory_read_ranges a.po_inst a.po_state) /\
       off_s <= j /\ j < off_s+len /\ j IN a.po_taint.t_mem` by
    (map_every qx_gen_tac [`off`,`len`,`i`] >> strip_tac >>
     `len <> 0` by decide_tac >>
     mp_tac (Q.INST [
       `fn` |-> `a.po_fn`, `ft` |-> `at.po_fn`,
       `inst` |-> `a.po_inst`, `G` |-> `a.po_prov`,
       `tn` |-> `a.po_taint`, `src` |-> `a.po_state`,
       `tgt` |-> `at.po_state`, `dyn` |-> `dyn_floor C vs`,
       `mops` |-> `mem_read_ops a.po_inst`,
       `ranges_s` |-> `source_memory_read_ranges a.po_inst a.po_state`,
       `ranges_t` |-> `source_memory_read_ranges a.po_inst at.po_state`]
       ptr_current_range_transport) >>
     (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
     disch_then (qx_choose_then `read_off` (fn th =>
       ASSUME_TAC (CONJUNCT1 th) THEN
       DISJ_CASES_THEN2 strip_assume_tac
         (qx_choose_then `read_ops`
           (qx_choose_then `read_x`
             (qx_choose_then `read_y` strip_assume_tac)))
         (CONJUNCT2 th)))
     >- (`read_off+len <= lo` by
           (mp_tac (Q.INST [
              `G` |-> `a.po_prov`, `fn` |-> `a.po_fn`,
              `inst` |-> `a.po_inst`, `s` |-> `a.po_state`,
              `off` |-> `read_off`, `len` |-> `len`,
              `mops` |-> `mem_read_ops a.po_inst`,
              `ranges` |->
                `source_memory_read_ranges a.po_inst a.po_state`]
              ptr_access_range_classification) >>
            (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
            qpat_assum `~(?ops. mem_read_ops a.po_inst = SOME ops /\
              op_prov a.po_prov ops.iao_ofst <> NONE)` (fn absent =>
              qpat_assum `len <> 0` (fn positive =>
                disch_then (fn classification =>
                  MAP_EVERY MP_TAC [absent,positive,classification]))) >>
            POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
            gvs[op_prov_def] >> metis_tac[]) >>
         `i < lo` by decide_tac >>
         `i IN a.po_taint.t_mem` by
           (qpat_assum `!i. (i < lo \/ dyn_floor C vs <= i) /\
              i IN at.po_taint.t_mem ==> i IN a.po_taint.t_mem` irule >>
            simp[]) >>
         qexistsl_tac [`read_off`,`i`] >> simp[]) >>
     qpat_assum `read_off = w2n read_x` (fn off_eq =>
       qpat_assum `MEM (read_off,len)
         (source_memory_read_ranges a.po_inst a.po_state)`
         (assume_tac o REWRITE_RULE[off_eq])) >>
     mp_tac (Q.INST [
       `a` |-> `a`, `at` |-> `at`, `ops` |-> `read_ops`,
       `x` |-> `read_x`, `y` |-> `read_y`, `n` |-> `len`]
       ptr_paired_current_range_classification_memory_static) >>
     (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
     disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
       (qx_choose_then `read_v`
         (qx_choose_then `read_token`
           (qx_choose_then `read_aid`
             (qx_choose_then `read_base`
               (qx_choose_then `read_size`
                 (qx_choose_then `read_pos` strip_assume_tac)))))))
     >- (qpat_assum `read_y = read_x` SUBST_ALL_TAC >>
         qpat_assum `off = w2n read_x` SUBST_ALL_TAC >>
         `i < lo \/ dyn_floor C vs <= i` by decide_tac >>
         `i IN a.po_taint.t_mem` by
           (qpat_assum `!i. (i < lo \/ dyn_floor C vs <= i) /\
              i IN at.po_taint.t_mem ==> i IN a.po_taint.t_mem` irule >>
            simp[]) >>
         qexistsl_tac [`read_off`,`i`] >> simp[]) >>
     `inst_read_op a.po_inst = SOME (Var read_v)` by
       simp[concretizeMemLocDefsTheory.inst_read_op_def] >>
     qpat_assum `inst_read_op a.po_inst = SOME (Var read_v)`
       (assume_tac o MATCH_MP ptr_read_op_operand) >>
     `a.po_inst.inst_opcode <> ASSIGN` by
       (strip_tac >> fs[mem_read_ops_def]) >>
     qabbrev_tac `read_ix = (w2n read_x-read_base)+(i-w2n read_y)` >>
     `read_ix < read_size /\ read_pos+read_ix = i /\
      read_base+read_ix = w2n read_x+(i-w2n read_y)` by
       (simp[Abbr`read_ix`] >> decide_tac) >>
     `w2n read_x <= read_base+read_ix /\
      read_base+read_ix < w2n read_x+len` by decide_tac >>
     qpat_assum `!v token aid base size pos ix.
       ~in_revert_forward a.po_fn a.po_state /\
       a.po_inst.inst_opcode <> ASSIGN /\
       MEM (Var v) a.po_inst.inst_operands /\
       (inst_read_op a.po_inst = SOME (Var v) \/
         a.po_inst.inst_opcode = INVOKE) /\
       FLOOKUP TG v = SOME (token,aid) /\
       FLOOKUP a.po_prov v = SOME (base,size) /\
       FLOOKUP births (token,aid) = SOME (base,size) /\
       FLOOKUP positions (Allocation aid) = SOME (pos,size) /\ ix < size ==>
       pos+ix IN at.po_taint.t_mem ==> base+ix IN a.po_taint.t_mem`
       (qspecl_then [`read_v`,`read_token`,`read_aid`,`read_base`,
         `read_size`,`read_pos`,`read_ix`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
     qexistsl_tac [`w2n read_x`,`read_base+read_ix`] >>
     asm_rewrite_tac[]) >>
  suspend "read_transport"
QED

Resume ptr_dalloca_paired_frame_ptr_static[read_transport]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  qpat_assum `~(a.po_inst.inst_opcode = RETURNDATACOPY \/
    a.po_inst.inst_opcode = REVERT)`
    (strip_assume_tac o REWRITE_RULE[DE_MORGAN_THM]) >>
  mp_tac (Q.INST [`fn` |-> `a.po_fn`, `ft` |-> `at.po_fn`,
    `inst` |-> `a.po_inst`, `tn` |-> `a.po_taint`, `tnt` |-> `at.po_taint`,
    `s` |-> `a.po_state`, `t` |-> `at.po_state`]
    ptr_dalloca_taint_transport) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[]
    >- simp[about_to_revert_def]
    >- (strip_tac >> qx_gen_tac `op` >> strip_tac >>
        mp_tac (Q.INST [`fn` |-> `a.po_fn`, `ft` |-> `at.po_fn`,
          `inst` |-> `a.po_inst`, `tn` |-> `a.po_taint`,
          `s` |-> `a.po_state`, `t` |-> `at.po_state`]
          (INST_TYPE [alpha |-> ``:num``] ptr_dalloca_mul_clean_demands)) >>
        (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
        disch_then (qspec_then `op` mp_tac) >> asm_rewrite_tac[] >>
        disch_then (ACCEPT_TAC o SYM)) >>
    metis_tac[])) >>
  disch_then ACCEPT_TAC
QED

Finalise ptr_dalloca_paired_frame_ptr_static

Theorem ptr_dalloca_paired_frame_ptr:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_paired_frame_ptr_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
