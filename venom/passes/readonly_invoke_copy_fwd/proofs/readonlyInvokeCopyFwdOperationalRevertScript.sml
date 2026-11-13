Theory readonlyInvokeCopyFwdOperationalRevert
Ancestors
  readonlyInvokeCopyFwdHistoryAbort readonlyInvokeCopyFwdStepsAborts
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel o1LowerDloadForwardInversion
  o1LowerDloadAvailableSuffix o1LowerDloadGhost o1LowerDloadOccurrence
  o1LowerDloadPtrDiscipline o1PassContract o1LowerDloadRelocationKernel
  ptrDiscipline taintAgree contextCodegenRel pointerConfinedDefs memLocDefs
  venomExecSemantics venomExecProofs venomExecProps venomState venomInst
  finite_map words list pred_set

Theorem ricf_operational_revert_forward:
  frame_reachable vs C stk PG G tn fn inst s /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  ptr_discipline lo C vs /\ vs.vs_allocas = FEMPTY /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  in_revert_forward fn s /\ ricf_block_edit bb bb' /\
  ricf_frame_agree D X sites PG G tn s t /\
  terminates (exec_block fuel C bb s) ==>
  ?reason se. exec_block fuel C bb s = Abort reason se /\
    !fuel' C'. ?te. exec_block fuel' C' bb' t = Abort reason te
Proof
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx` by gvs[in_revert_forward_def] >>
  `?reason se. exec_block fuel C bb s = Abort reason se` by
    metis_tac[revert_forward_at_terminates_abort] >>
  `s.vs_inst_idx = t.vs_inst_idx /\ s.vs_labels = t.vs_labels /\
   FDOM s.vs_vars = FDOM t.vs_vars` by
    gvs[ricf_frame_agree_def, taint_agree_def, venom_state_component_equality] >>
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

Resume ricf_operational_revert_forward[copy]:
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
    (gen_tac >> irule ld_available_operand >> simp[] >>
     qexists_tac `UNIV` >> simp[FLOOKUP_DEF] >>
     gen_tac >> IF_CASES_TAC >> simp[]) >>
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
     drule ricf_frame_agree_operand >>
     disch_then (qspecl_then [`x`, `op`] mp_tac) >>
     simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_bits] >>
     strip_tac >> `x = y` by simp[Once fcpTheory.CART_EQ] >> simp[]) >>
  `s.vs_returndata = t.vs_returndata` by
    gvs[ricf_frame_agree_def, taint_agree_def, venom_state_component_equality] >>
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

Finalise ricf_operational_revert_forward
