Theory readonlyInvokeCopyFwdExecutionForward
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionBoundary
  frameRelocationGuardedValues allocaFrontierBound
  readonlyInvokeCopyFwdExecutionCoverage frameViewFacts
  reachableFnSim passSimulationDefs arithmetic
  readonlyInvokeCopyFwdHistoryAbort readonlyInvokeCopyFwdStepsAborts
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel o1LowerDloadForwardInversion
  o1LowerDloadAvailableSuffix o1LowerDloadGhost o1LowerDloadOccurrence
  o1LowerDloadPtrDiscipline o1PassContract o1LowerDloadRelocationKernel
  ptrDiscipline taintAgree contextCodegenRel pointerConfinedDefs memLocDefs
  venomExecSemantics venomExecProofs venomExecProps venomInstProofs venomState venomInst
  finite_map words list pred_set

Theorem ricf_execution_revert_forward:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  in_revert_forward fn s /\ ricf_block_edit bb bb' /\
  terminates (exec_block fuel C bb s) ==>
  ?reason se. exec_block fuel C bb s = Abort reason se /\
    !fuel' C'. ?te. exec_block fuel' C' bb' t = Abort reason te
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `revert_forward_at bb s.vs_inst_idx` by gvs[in_revert_forward_def] >>
  `?reason se. exec_block fuel C bb s = Abort reason se` by
    metis_tac[revert_forward_at_terminates_abort] >>
  `s.vs_inst_idx = t.vs_inst_idx /\ s.vs_labels = t.vs_labels /\
   FDOM s.vs_vars = FDOM t.vs_vars` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_labels >>
     gvs[ricf_opaque_view_def, taint_agree_def, venom_state_component_equality]) >>
  qexistsl_tac [`reason`, `se`] >> simp[] >>
  fs[revert_forward_at_def]
  >- suspend "copy" >>
  `inst.inst_opcode = REVERT` by gvs[revert_forward_pair_def] >>
  rpt gen_tac >>
  drule_at (Pat `exec_block _ _ _ _ = _`) ld_available_suffix_abort_fuel >>
  disch_then irule >> (conj_tac >- simp[]) >> qexistsl_tac [`UNIV`, `0`, `inst`] >>
  simp[FLOOKUP_DEF] >> conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
  sym_tac >> irule ricf_block_edit_unchanged_fetch >>
  simp[] >> qexists_tac `bb` >> simp[]
QED

Resume ricf_execution_revert_forward[copy]:
  `active_inst fn inst s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  qpat_assum `revert_forward_pair _ _ _`
    (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
  gvs[] >>
  `!op. IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t)` by
    (gen_tac >> metis_tac[ricf_opaque_frame_operand_defined]) >>
  `!op. op = src \/ op = rds ==> eval_operand op s = eval_operand op t` by
    (gen_tac >> disch_tac >>
     `op_prov G op = NONE` by
       (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
        Cases_on `FLOOKUP G vv` >> simp[] >>
        `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
        qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
        gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
            mem_write_ops_def, mem_read_ops_def] >> qexists_tac `vv` >>
        Cases_on `p = Var vv` >> Cases_on `src = Var vv` >>
        Cases_on `rds = Var vv` >> simp[] >> rpt strip_tac >> gvs[]) >>
     `op_taint tn op = {}` by
       (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
        gvs[taint_ok_def] >> metis_tac[]) >>
     Cases_on `eval_operand op s`
     >- (qpat_x_assum `!op. IS_SOME _ <=> _` (qspec_then `op` mp_tac) >>
         Cases_on `eval_operand op t` >> simp[]) >>
     `!name. op = Var name ==> ~retpc_var fn name` by
       (rpt gen_tac >> strip_tac >>
        irule ordinary_operand_not_retpc >> simp[] >>
        qexists_tac `inst` >> simp[MEM] >>
        metis_tac[active_inst_mem_fn_insts]) >>
     drule_all ricf_opaque_frame_operand >> strip_tac >>
     `x = y` by
       gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
           ricf_value_agree_def, ld_value_agree_def, word_agree_except_empty] >>
     simp[]) >>
  `s.vs_returndata = t.vs_returndata` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\st. st.vs_returndata`) >>
     simp[ricf_opaque_view_def]) >>
  `get_instruction bb' t.vs_inst_idx = SOME inst` by
    (irule ricf_block_edit_unchanged_fetch >> simp[] >>
     qexists_tac `bb` >> simp[]) >>
  `IS_SOME (eval_operand p s) <=> IS_SOME (eval_operand p t)` by metis_tac[] >>
  `eval_operand src s = eval_operand src t /\
   eval_operand rds s = eval_operand rds t` by metis_tac[] >>
  rpt gen_tac >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  (Cases_on `eval_operand p t`
   >- (qpat_x_assum `!op. IS_SOME _ <=> _` (qspec_then `p` mp_tac) >> gvs[]) >>
   rename1 `eval_operand p t = SOME target_dest` >>
   pure_once_rewrite_tac[exec_block_def] >> pure_asm_rewrite_tac[] >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[is_terminator_def] >>
   qpat_x_assum `write_memory_with_expansion _ _ s = s''` (SUBST_ALL_TAC o SYM) >>
   drule_at (Pat `exec_block _ _ _ _ = _`) ld_available_suffix_abort_fuel >>
   disch_then irule >>
   simp[write_memory_with_expansion_def, write_memory_def] >>
   qexistsl_tac [`UNIV`, `j - SUC t.vs_inst_idx`, `inst2`] >>
   simp[] >>
   (conj_tac
   >- (rpt strip_tac >> simp[FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]) >>
   conj_tac
   >- (rpt strip_tac >> first_x_assum irule >>
       qexists_tac `k + SUC t.vs_inst_idx` >> simp[] >> decide_tac) >>
   rpt strip_tac >>
   Cases_on `get_instruction bb (k + SUC t.vs_inst_idx)`
   >- (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac) >>
   rename1 `get_instruction bb (k + SUC t.vs_inst_idx) = SOME ii` >>
   `ii.inst_opcode = ASSIGN \/ ii.inst_opcode = REVERT` by
     (Cases_on `k + SUC t.vs_inst_idx = j` >- gvs[] >>
      disj1_tac >> first_x_assum irule >>
      qexists_tac `k + SUC t.vs_inst_idx` >> simp[] >> decide_tac) >>
   sym_tac >> irule ricf_block_edit_unchanged_fetch >>
   simp[] >> qexists_tac `bb` >> simp[]))
QED

Finalise ricf_execution_revert_forward

Theorem ricf_execution_point_revert_forward:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  in_revert_forward fn s /\ ricf_block_edit bb tb /\
  terminates (exec_block fuel C bb s) ==>
  ?reason se te. exec_block fuel C bb s = Abort reason se /\
    exec_block 0 Ct tb t = Abort reason te
Proof
  rw[ricf_execution_point_def] >>
  drule_all ricf_execution_revert_forward >> strip_tac >>
  qexistsl_tac [`reason`,`se`] >> simp[]
QED

Theorem ricf_execution_exec_block_forward:
  ((!G tn inst s t.
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      in_revert_forward fn s /\ terminates (exec_block k C bb s) ==>
      ?reason se m te. exec_block k C bb s = Abort reason se /\
        exec_block m Ct tb t = Abort reason te) /\
   (!G tn inst ti s t.
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      terminates (step_inst k C inst s) /\
      (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
      ?m. block_step_rel D vs C
        (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
        stk PG fn (step_inst k C inst s) (step_inst m Ct ti t)) /\
   (!G tn inst ti s t u next.
      ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
        stk PG G tn fn inst s t /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction tb t.vs_inst_idx = SOME ti /\
      ~in_revert_forward fn s /\
      ~is_terminator inst.inst_opcode /\ step_inst k C inst s = OK u /\
      active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ?h v G1 tn1.
        step_inst h Ct ti t = OK v /\
        ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
          stk PG G1 tn1 fn next
          (u with vs_inst_idx := SUC s.vs_inst_idx)
          (v with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  !G tn inst s t.
    ricf_block_edit bb tb /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG G tn fn inst s t /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    terminates (exec_block k C bb s) ==>
    ?m. block_step_rel D vs C
      (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      stk PG fn (exec_block k C bb s) (exec_block m Ct tb t)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "forward")
    (CONJUNCTS_THEN2 (mk_asm "terminal") (mk_asm "next"))) >>
  rpt gen_tac >> map_every qid_spec_tac [`inst`,`t`,`tn`,`G`] >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  `s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `?ti. get_instruction tb t.vs_inst_idx = SOME ti /\
    (is_terminator ti.inst_opcode <=> is_terminator inst.inst_opcode)` by
    metis_tac[ricf_block_edit_fetch] >>
  Cases_on `in_revert_forward fn s`
  >- (asm "forward" (qspecl_then [`G`,`tn`,`inst`,`s`,`t`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >> qexists_tac `m` >>
      simp[block_step_rel_def, fn_run_rel_def, dead_result_rel_def]) >>
  `terminates (step_inst k C inst s)` by
    (qpat_x_assum `terminates (exec_block _ _ _ _)` mp_tac >>
     simp[Once exec_block_def] >> Cases_on `step_inst k C inst s` >>
     simp[terminates_def]) >>
  Cases_on `!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode`
  >- (asm "terminal" (qspecl_then [`G`,`tn`,`inst`,`ti`,`s`,`t`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >> qexists_tac `m` >>
      irule ricf_execution_terminal_suffix >> metis_tac[]) >>
  gvs[] >> rename1 `step_inst k C inst s = OK u` >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `terminates (exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates (exec_block _ _ _ s)` mp_tac >>
     simp[Once exec_block_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (conj_tac >- fs[get_instruction_def] >> spose_not_then assume_tac >>
     qpat_x_assum `terminates (exec_block _ _ _ _)` mp_tac >>
     simp[Once exec_block_def, get_instruction_def, terminates_def]) >>
  `active_inst fn (EL (SUC s.vs_inst_idx) bb.bb_instructions)
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[active_inst_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  asm "next" (qspecl_then [`G`,`tn`,`inst`,`ti`,`s`,`t`,`u`,
    `EL (SUC s.vs_inst_idx) bb.bb_instructions`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  asm_x "forward" kall_tac >>
  asm_x "terminal" kall_tac >> asm_x "next" kall_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`G1`,`tn1`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `EL (SUC s.vs_inst_idx) bb.bb_instructions`] mp_tac) >>
  simp[get_instruction_def] >> impl_tac >- metis_tac[] >> strip_tac >>
  `!e. exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
    (Cases_on `exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
     Cases_on `exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
     gvs[block_step_rel_def, fn_run_rel_def]) >>
  `step_inst (MAX h m) Ct ti t = OK v` by
    (irule (CONJUNCT1 fuel_mono) >> simp[] >> qexists_tac `h` >> simp[]) >>
  `exec_block (MAX h m) Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx) =
    exec_block m Ct tb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (CONJUNCT1 (CONJUNCT2 fuel_mono)) >> simp[] >>
     qexists_tac `m` >> simp[]) >>
  qexists_tac `MAX h m` >> once_rewrite_tac[exec_block_def] >> simp[] >> gvs[]
QED
