Theory concretizePtrDallocaPairedObservation
Ancestors
  concretizePtrDallocaFinalObservation concretizePtrDallocaHaltSteps
  concretizePtrDallocaGhostHistory concretizePtrDallocaGhostInterface
  concretizePtrCallFamily concretizePtrOrdinaryNext concretizePtrObservationInterface
  concretizePtrMloadRecovery concretizePtrMloadEndpoint concretizePtrReturnTransport
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding
  concretizePtrSourceOwnership concretizePtrParamSupport concretizePtrOwnershipErasure
  concretizePtrAllocationSize concretizePtrPrefixLedger
  concretizePtrRequestHistory concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizeStepStructure concretizeStepShape concretizeLayoutLocalReturn
  lowerDloadRequestObservation ptrDiscipline ptrStaticDiscipline
  o1PassContract unitShapeDefs unitLabelMapIdentity contextCodegenRel
  memLocDefs concretizeMemLocDefs pointerConfinedDefs opcodeClass
  venomExecProofs
  venomExecSemantics venomInstProofs venomInstProofs1 venomWf venomInst venomState
  list rich_list arithmetic finite_map pred_set words

(* Both observations use the same actual stage bridge and endpoint ledger.
   In particular, a request bound is obtained from an actual source step. *)
Theorem ptr_dalloca_paired_observation_taint_static:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  (!fuelt post. at.po_inst.inst_opcode <> INVOKE /\
    step_inst fuelt C' at.po_inst at.po_state = OK post /\
    LENGTH at.po_state.vs_requests < LENGTH post.vs_requests ==>
    at.po_taint.t_stor SUBSET D.d_stor at.po_state.vs_call_ctx.cc_address
      (at.po_state.vs_accounts at.po_state.vs_call_ctx.cc_address).storage /\
    at.po_taint.t_trans SUBSET D.d_trans at.po_state.vs_call_ctx.cc_address
      (at.po_state.vs_transient at.po_state.vs_call_ctx.cc_address)) /\
  (!fuelt th. at.po_inst.inst_opcode <> INVOKE /\
    step_inst fuelt C' at.po_inst at.po_state = Halt th ==>
    (step_taint at.po_inst at.po_state th at.po_taint).t_stor SUBSET
      D.d_stor th.vs_call_ctx.cc_address
        (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
    (step_taint at.po_inst at.po_state th at.po_taint).t_trans SUBSET
      D.d_trans th.vs_call_ctx.cc_address (th.vs_transient th.vs_call_ctx.cc_address) /\
    (step_taint at.po_inst at.po_state th at.po_taint).t_imm SUBSET
      D.d_imm th.vs_immutables /\
    ret_taint at.po_taint at.po_inst at.po_state SUBSET D.d_ret th.vs_returndata)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    (qpat_assum `ptr_chrono_history vs C h a`
       (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[ptr_observation_reachable_def]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable vs C _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `active_inst at.po_fn at.po_inst at.po_state` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     qpat_x_assum `frame_reachable vs C' _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule_all ptr_frame_sizes_static >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ opaque_use_ok a.po_fn /\
   ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        fn_inst_wf_def, fn_shape_ok_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def,
        fn_insts_MEM] >> metis_tac[]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `fn_ptr_ok P a.po_fn /\ ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  qpat_assum `ptr_paired_sample positions a at _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_sample_def]) >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (drule ptr_history_content_labels >> simp[]) >>
  `h <> [] /\ LAST h = a` by
    (qpat_assum `ptr_chrono_history vs C h a`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >> simp[]) >>
  `ht <> [] /\ LAST ht = at` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >> simp[]) >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `H <> []` by (strip_tac >> gvs[]) >>
  `LENGTH h - 1 < LENGTH h /\ LENGTH ht - 1 = LENGTH done /\
   LENGTH H - 1 = LENGTH h - 1` by decide_tac >>
  `EL (LENGTH done) ht = at /\ EL (LENGTH h - 1) h = a /\
   EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (qpat_x_assum `LAST ht = at` mp_tac >>
     qpat_x_assum `LAST h = a` mp_tac >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `LENGTH done = 0 \/ EL (LENGTH done - 1) done < LENGTH h - 1` by
    (Cases_on `LENGTH done = 0` >- fs[] >>
     `LENGTH done - 1 < LENGTH done` by decide_tac >>
     qpat_assum `ptr_event_embedding h ht (done ++ [LENGTH h - 1])`
       (mp_tac o List.last o CONJUNCTS o REWRITE_RULE [ptr_event_embedding_def]) >>
     disch_then (qspecl_then [`LENGTH done - 1`,`LENGTH done`] mp_tac) >>
     fs[EL_APPEND_EQN]) >>
  `LENGTH h - 1 <= EL (LENGTH done) (done ++ [LENGTH h - 1])` by
    simp[EL_APPEND_EQN] >>
  mp_tac (Q.INST [`endpoint` |-> `a`] ptr_dalloca_ghost_history_static) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`LENGTH h - 1`,`LENGTH done`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> fs[])) >>
  disch_then (qspecl_then [`tokens`,`registry`,`births`,`PT`,`TG`,`saved`,`entries`]
    mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL (LENGTH h - 1) h = a` (fn source_end =>
    qpat_assum `EL (LENGTH done) ht = at` (fn target_end =>
      disch_then (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE [source_end,target_end]))) >>
  qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY births
      (\token aid. F) a at`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def]) >>
  suspend "observations"
QED

Resume ptr_dalloca_paired_observation_taint_static[observations]:
  markerLib.RESUME_TAC >> (conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM at.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by
        (drule_all ld_request_growth_external >> simp[]) >>
      `~MEM at.po_inst.inst_opcode [ASSIGN;NOP]` by
        (qpat_assum `MEM at.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
           (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[]) >>
      `at.po_inst = a.po_inst` by
        (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
           (fn th => once_rewrite_tac[th] >>
             irule concretize_positions_other_opcode >>
             rewrite_tac[GSYM th] >> first_assum ACCEPT_TAC)) >>
      `a.po_inst.inst_opcode <> INVOKE` by fs[] >>
      Cases_on `MEM a.po_inst.inst_opcode [CALL;STATICCALL]`
      >- (`~is_terminator at.po_inst.inst_opcode` by fs[is_terminator_def] >>
          `EVERY bb_well_formed at.po_fn.fn_blocks` by
            (`wf_function a.po_fn` by
               (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
             drule concretize_positions_preserves_wf >>
             disch_then (qspec_then `lp a.po_fn` assume_tac) >>
             fs[ptr_paired_code_def, wf_function_def, EVERY_MEM]) >>
          `post.vs_current_bb = at.po_state.vs_current_bb` by
            (drule venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
          `?next. active_inst at.po_fn next
             (post with vs_inst_idx := SUC at.po_state.vs_inst_idx)` by
            (irule ptr_ordinary_next_active >> metis_tac[]) >>
          qabbrev_tac `zt = ptr_observe at.po_stack at.po_params
            (step_prov at.po_params at.po_prov at.po_inst post)
            (step_taint at.po_inst at.po_state post at.po_taint) at.po_fn next
            (post with vs_inst_idx := SUC at.po_state.vs_inst_idx)` >>
          `ptr_observe at.po_stack at.po_params at.po_prov at.po_taint
             at.po_fn at.po_inst at.po_state = at` by
            simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
          `ptr_chrono_step C' at zt` by
            (mp_tac (Q.INST [`ctx` |-> `C'`, `stk` |-> `at.po_stack`,
               `PG` |-> `at.po_params`, `G` |-> `at.po_prov`,
               `tn` |-> `at.po_taint`, `fn` |-> `at.po_fn`,
               `inst` |-> `at.po_inst`, `inst'` |-> `next`,
               `s` |-> `at.po_state`, `s'` |-> `post`, `fuel` |-> `fuelt`]
               (SPEC_ALL (cj 1 ptr_chrono_step_rules))) >>
             simp[Abbr`zt`]) >>
          drule_all ptr_paired_call_step_static >>
          disch_then (qx_choose_then `srcpost` strip_assume_tac) >>
          mp_tac (Q.INST [`CS` |-> `C`, `stk` |-> `a.po_stack`,
            `PG` |-> `a.po_params`, `G` |-> `a.po_prov`,
            `tn` |-> `a.po_taint`, `fn` |-> `a.po_fn`, `inst` |-> `a.po_inst`,
            `s` |-> `a.po_state`, `post` |-> `srcpost`, `fuel` |-> `0`,
            `t` |-> `at.po_state`, `un` |-> `at.po_taint`,
            `nextn` |-> `step_taint a.po_inst a.po_state srcpost a.po_taint`,
            `nextt` |-> `zt.po_state`] ptr_dalloca_actual_request_observation) >>
          (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[] >>
            simp[Abbr`zt`, ptr_observe_def])) >> simp[]) >>
      `a.po_taint.t_stor = {} /\ a.po_taint.t_trans = {}` by
        (fs[MEM, taint_ok_def] >> metis_tac[]) >>
      fs[SUBSET_EMPTY]) >>
  rpt gen_tac >> strip_tac >>
  `MEM at.po_inst.inst_opcode [STOP;RETURN;SINK;SELFDESTRUCT]` by
    (drule step_inst_halt_opcodes >> simp[]) >>
  `~MEM at.po_inst.inst_opcode [ASSIGN;NOP]` by
    (qpat_assum `MEM at.po_inst.inst_opcode [STOP;RETURN;SINK;SELFDESTRUCT]`
       (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[]) >>
  `at.po_inst = a.po_inst` by
    (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
       (fn th => once_rewrite_tac[th] >>
         irule concretize_positions_other_opcode >>
         rewrite_tac[GSYM th] >> first_assum ACCEPT_TAC)) >>
  `a.po_inst.inst_opcode <> INVOKE` by fs[] >>
  `~in_revert_forward a.po_fn a.po_state` by
    (irule active_inst_not_revert_forward >> simp[] >>
     qexists_tac `a.po_inst` >> fs[MEM]) >>
  suspend "halt")
QED

Resume ptr_dalloca_paired_observation_taint_static[halt]:
  markerLib.RESUME_TAC >> (
  `(at.po_inst.inst_opcode = SINK ==>
      a.po_state.vs_returndata = at.po_state.vs_returndata)` by
    (drule ptr_history_content_returndata >> simp[]) >>
  `(at.po_inst.inst_opcode = SELFDESTRUCT ==>
      a.po_state.vs_call_ctx.cc_static = at.po_state.vs_call_ctx.cc_static /\
      eval_operands a.po_inst.inst_operands a.po_state =
        eval_operands at.po_inst.inst_operands at.po_state)` by
    (strip_tac >>
     `a.po_inst.inst_opcode = SELFDESTRUCT` by metis_tac[] >>
     `a.po_state.vs_call_ctx = at.po_state.vs_call_ctx` by
       (drule ptr_history_content_call_ctx >> simp[]) >> simp[] >>
     `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
     `!v. MEM (Var v) a.po_inst.inst_operands ==> v NOTIN fn_pv P a.po_fn` by
       (qpat_x_assum `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` mp_tac >>
        simp[ptr_use_ok_def, is_pointer_preserving_op_def,
             mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
     mp_tac (Q.INST [`ops` |-> `a.po_inst.inst_operands`,
       `tn` |-> `a.po_taint`, `f` |-> `a.po_fn`, `g` |-> `at.po_fn`,
       `s` |-> `a.po_state`, `t` |-> `at.po_state`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:num``]
         ptr_mixed_scalar_operands_equal))) >>
     (impl_tac >- (simp[] >> simp[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     `ptr_nonopaque_operand a.po_fn op` by fs[EVERY_MEM] >> simp[] >>
     `op_prov a.po_prov op = NONE` by
       (Cases_on `op` >> simp[op_prov_def] >>
        rename1 `FLOOKUP a.po_prov v = NONE` >>
        Cases_on `FLOOKUP a.po_prov v` >> simp[] >>
        fs[FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
     `op_prov TG op = NONE` by
       (drule ptr_owner_op_projection >>
        disch_then (qspec_then `op` mp_tac) >>
        Cases_on `op_prov TG op` >> simp[ptr_owner_erases_def, FLOOKUP_DEF]) >>
     simp[] >> qpat_assum `taint_ok a.po_fn a.po_taint a.po_inst a.po_state`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [taint_ok_def]) >>
     disch_then (qspec_then `op` mp_tac) >> simp[])) >> simp[]) >>
  suspend "return")
QED

Resume ptr_dalloca_paired_observation_taint_static[return]:
  markerLib.RESUME_TAC >> (
  `(at.po_inst.inst_opcode = RETURN ==>
    ?addr lenop offsrc offtgt readsz.
      a.po_inst.inst_operands = [addr;lenop] /\
      at.po_inst.inst_operands = [addr;lenop] /\
      eval_operand addr a.po_state = SOME offsrc /\
      eval_operand lenop a.po_state = SOME readsz /\
      eval_operand addr at.po_state = SOME offtgt /\
      eval_operand lenop at.po_state = SOME readsz /\
      (!i. i < w2n readsz /\ w2n offtgt + i IN at.po_taint.t_mem ==>
        w2n offsrc + i IN a.po_taint.t_mem) /\
      (!i. i < w2n readsz /\ w2n offsrc + i NOTIN a.po_taint.t_mem ==>
        read_byte (w2n offsrc + i) a.po_state.vs_memory =
        read_byte (w2n offtgt + i) at.po_state.vs_memory))` by
    (strip_tac >>
     `a.po_inst.inst_opcode = RETURN` by metis_tac[] >>
     `?addr lenop. a.po_inst.inst_operands = [addr;lenop]` by
       (fs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
     `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
     `ptr_nonopaque_operand a.po_fn addr /\ ptr_nonopaque_operand a.po_fn lenop` by
       (qpat_assum `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands`
          (fn th => qpat_assum `a.po_inst.inst_operands = [addr;lenop]`
            (fn eq => ACCEPT_TAC (SIMP_RULE (srw_ss()) [eq] th)))) >>
     `?yt target_size. eval_operand addr at.po_state = SOME yt /\
       eval_operand lenop at.po_state = SOME target_size` by
       (qpat_x_assum `step_inst fuelt C' at.po_inst at.po_state = Halt th` mp_tac >>
        simp[Once step_inst_non_invoke, step_inst_base_def,
             eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
     `MEM (w2n yt,w2n target_size) (source_memory_read_ranges a.po_inst at.po_state)` by
       simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
     mp_tac (Q.INST [`dyn` |-> `dyn_floor C vs`, `G` |-> `a.po_prov`,
       `tn` |-> `a.po_taint`, `f` |-> `a.po_fn`, `g` |-> `at.po_fn`,
       `s` |-> `a.po_state`, `t` |-> `at.po_state`, `inst` |-> `a.po_inst`,
       `pv` |-> `fn_pv P a.po_fn`, `off` |-> `w2n (yt:256 word)`,
       `len` |-> `w2n (target_size:256 word)`]
       ptr_terminal_read_range_transport) >>
     (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
     disch_then (qx_choose_then `offsrc` (qx_choose_then `offtgt`
       (qx_choose_then `readsz` strip_assume_tac))) >>
     qpat_assum `w2n target_size = w2n readsz`
       (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
     qabbrev_tac `readops =
       <|iao_ofst := addr; iao_size := SOME lenop; iao_max_size := SOME lenop|>` >>
     `mem_read_ops a.po_inst = SOME readops /\
      inst_read_op a.po_inst = SOME readops.iao_ofst /\
      MEM readops.iao_ofst a.po_inst.inst_operands /\
      eval_operand readops.iao_ofst a.po_state = SOME offsrc /\
      eval_operand readops.iao_ofst at.po_state = SOME offtgt /\
      MEM (w2n offsrc,w2n readsz) (source_memory_read_ranges a.po_inst a.po_state) /\
      ptr_lookup_transport births positions (op_prov TG readops.iao_ofst) {}
        (SOME offsrc) (SOME offtgt)` by
       simp[Abbr`readops`, mem_read_ops_def, inst_read_op_def] >>
     `a.po_inst.inst_opcode <> ASSIGN` by fs[] >>
     `!i. i < w2n readsz /\ w2n offsrc + i NOTIN a.po_taint.t_mem ==>
       read_byte (w2n offsrc+i) a.po_state.vs_memory =
       read_byte (w2n offtgt+i) at.po_state.vs_memory` by
       (mp_tac (Q.INST [`ops` |-> `readops`, `x` |-> `offsrc`,
          `y` |-> `offtgt`, `n` |-> `w2n (readsz:256 word)`]
          ptr_paired_read_range_masked_bytes_static) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     qexistsl_tac [`addr`,`lenop`,`offsrc`,`offtgt`,`readsz`] >> simp[] >>
     gen_tac >> strip_tac >>
     `w2n readsz <> 0` by decide_tac >>
     mp_tac (Q.INST [`ops` |-> `readops`, `x` |-> `offsrc`,
       `y` |-> `offtgt`, `n` |-> `w2n (readsz:256 word)`]
       ptr_paired_read_range_classification_static) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
       (qx_choose_then `rv` (qx_choose_then `rtok` (qx_choose_then `raid`
         (qx_choose_then `rb` (qx_choose_then `rsize`
           (qx_choose_then `rpos` strip_assume_tac)))))))
     >- (qpat_assum `!i. (i < lo \/ dyn_floor C vs <= i) /\
           i IN at.po_taint.t_mem ==> i IN a.po_taint.t_mem`
           (qspec_then `w2n (offtgt:256 word)+i` mp_tac) >>
         qpat_assum `offtgt = offsrc` mp_tac >>
         qpat_assum `i + w2n offtgt IN at.po_taint.t_mem` mp_tac >>
         qpat_assum `i < w2n readsz` mp_tac >>
         qpat_assum `w2n offsrc + w2n readsz <= lo \/
           dyn_floor C vs <= w2n offsrc` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[ADD_COMM] >>
         first_x_assum irule >> simp[] >> decide_tac) >>
     `addr = Var rv` by fs[Abbr`readops`] >>
     `inst_read_op a.po_inst = SOME (Var rv) /\
      MEM (Var rv) a.po_inst.inst_operands` by
       simp[inst_read_op_def] >>
     qabbrev_tac `ix = (w2n offsrc-rb)+i` >>
     `ix < rsize /\ rpos+ix = w2n offtgt+i /\ rb+ix = w2n offsrc+i` by
       (simp[Abbr`ix`] >> decide_tac) >>
     qpat_assum `!v token aid base size pos ix.
       ~in_revert_forward a.po_fn a.po_state /\
       a.po_inst.inst_opcode <> ASSIGN /\ MEM (Var v) a.po_inst.inst_operands /\
       (inst_read_op a.po_inst = SOME (Var v) \/ a.po_inst.inst_opcode = INVOKE) /\
       FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (base,size) /\
       FLOOKUP births (token,aid) = SOME (base,size) /\
       FLOOKUP positions (Allocation aid) = SOME (pos,size) /\ ix < size ==>
       pos+ix IN at.po_taint.t_mem ==> base+ix IN a.po_taint.t_mem`
       (qspecl_then [`rv`,`rtok`,`raid`,`rb`,`rsize`,`rpos`,`ix`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC, disj1_tac >> first_assum ACCEPT_TAC])) >>
     qpat_assum `rpos+ix = w2n offtgt+i` (fn eq => rewrite_tac[eq]) >>
     qpat_assum `rb+ix = w2n offsrc+i` (fn eq => rewrite_tac[eq]) >>
     simp[NoAsms, ADD_COMM] >> disch_then MATCH_MP_TAC >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`CS` |-> `C`, `CT` |-> `C'`,
    `stk` |-> `a.po_stack`, `PG` |-> `a.po_params`, `G` |-> `a.po_prov`,
    `tn` |-> `a.po_taint`, `fn` |-> `a.po_fn`, `inst` |-> `a.po_inst`,
    `s` |-> `a.po_state`, `it` |-> `at.po_inst`, `t` |-> `at.po_state`,
    `un` |-> `at.po_taint`, `fuel` |-> `0`] ptr_dalloca_halt_step) >>
  (impl_tac >- (asm_rewrite_tac[] >> strip_tac >>
    `at.po_inst.inst_opcode = RETURN` by
      (qpat_assum `at.po_inst = a.po_inst`
         (fn eq => rewrite_tac[eq] >> first_assum ACCEPT_TAC)) >>
    qpat_assum `at.po_inst.inst_opcode = RETURN ==>
      ?addr lenop offsrc offtgt readsz. _`
      (fn th => qpat_assum `at.po_inst.inst_opcode = RETURN`
        (mp_tac o MP th)) >>
    disch_then (qx_choose_then `addr` (qx_choose_then `lenop`
      (qx_choose_then `offsrc` (qx_choose_then `offtgt`
        (qx_choose_then `readsz` strip_assume_tac))))) >>
    qexistsl_tac [`addr`,`lenop`,`addr`,`lenop`,`offsrc`,`offtgt`,`readsz`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sh` strip_assume_tac) >>
  mp_tac (Q.INST [`CS` |-> `C`, `CT` |-> `C'`,
    `inst` |-> `a.po_inst`, `s` |-> `a.po_state`, `tn` |-> `a.po_taint`,
    `it` |-> `at.po_inst`, `t` |-> `at.po_state`, `un` |-> `at.po_taint`,
    `fuel` |-> `0`] ptr_dalloca_actual_final_observation) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[])
QED

Finalise ptr_dalloca_paired_observation_taint_static

Theorem ptr_dalloca_paired_observation_taint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  (!fuelt post. at.po_inst.inst_opcode <> INVOKE /\
    step_inst fuelt C' at.po_inst at.po_state = OK post /\
    LENGTH at.po_state.vs_requests < LENGTH post.vs_requests ==>
    at.po_taint.t_stor SUBSET D.d_stor at.po_state.vs_call_ctx.cc_address
      (at.po_state.vs_accounts at.po_state.vs_call_ctx.cc_address).storage /\
    at.po_taint.t_trans SUBSET D.d_trans at.po_state.vs_call_ctx.cc_address
      (at.po_state.vs_transient at.po_state.vs_call_ctx.cc_address)) /\
  (!fuelt th. at.po_inst.inst_opcode <> INVOKE /\
    step_inst fuelt C' at.po_inst at.po_state = Halt th ==>
    (step_taint at.po_inst at.po_state th at.po_taint).t_stor SUBSET
      D.d_stor th.vs_call_ctx.cc_address
        (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
    (step_taint at.po_inst at.po_state th at.po_taint).t_trans SUBSET
      D.d_trans th.vs_call_ctx.cc_address (th.vs_transient th.vs_call_ctx.cc_address) /\
    (step_taint at.po_inst at.po_state th at.po_taint).t_imm SUBSET
      D.d_imm th.vs_immutables /\
    ret_taint at.po_taint at.po_inst at.po_state SUBSET D.d_ret th.vs_returndata)
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_paired_observation_taint_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
