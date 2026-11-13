Theory o1LowerDloadNonCallContinuation
Ancestors
  o1LowerDloadSegmentContinuation o1LowerDloadSuppliedSegmentNext
  o1LowerDloadUnchangedFetch o1LowerDloadOrdinaryDispatch
  o1LowerDloadFreshNext o1LowerDloadRepeatedNext
  o1LowerDloadJointRelation o1LowerDloadReadiness o1LowerDloadOccurrence
  o1PassContract ptrDiscipline venomExecSemantics venomInstProps venomWf
  contextCodegenRel venomInst venomExecProps irSupply list finite_map

Theorem ld_joint_singleton_continue[local]:
  !bb.
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 tnext fn' bb' B1 sites1 X1.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!m. exec_block m C' bb' t = exec_block m C' bb' tnext) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) tnext
      n a U B1 HP (occurrence_step a HP H inst s1) sites1 X1 ts
Proof
  rpt gen_tac >> strip_tac >>
  `mem_inv dload_offset_ok C vs /\ mem_inv dload_headroom_ok C vs` by
    fs[o1_src_inv_def] >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn /\ fn_inst_wf fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `?next. active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_nonterminator_successor >>
     drule_all step_preserves_control_flow >> simp[] >> metis_tac[]) >>
  `?inst2 t1 B1 sites1.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    step_inst fuel C' inst t = OK t1 /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B1 HP (occurrence_step a HP H inst s1) sites1 X ts` by
    (Cases_on `inst.inst_opcode = ALLOCA`
     >- (`MEM inst (fn_insts fn)` by
           (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
         `inst_wf inst` by
           (fs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
            fs[EVERY_MEM, active_inst_def] >> metis_tac[MEM_EL]) >>
         `?amount out. inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out]` by
           (qpat_x_assum `inst_wf inst` mp_tac >>
            simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
         `MEM inst.inst_id (fn_ir_inst_ids fn)` by
           (`MEM bb fn.fn_blocks` by
              metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
            `MEM inst bb.bb_instructions` by
              (fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
            simp[fn_ir_inst_ids_def, block_ir_inst_ids_def, MEM_FLAT, MEM_MAP] >>
            qexists_tac `MAP (\i. i.inst_id) bb.bb_instructions` >>
            simp[MEM_MAP] >> metis_tac[]) >>
         Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
         >- (drule_all ld_joint_alloca_fresh_next >> strip_tac >> metis_tac[]) >>
         rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME site` >>
         PairCases_on `site` >>
         drule_all ld_joint_alloca_repeated_next >> strip_tac >>
         qexistsl_tac [`next`,`t1`,`B`,`sites`] >> simp[])
     >> `~MEM inst.inst_opcode [INVOKE; DLOAD; DLOADBYTES; ALLOCA]` by simp[] >>
     drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_joint_ordinary_next >>
     simp[] >> disch_then drule_all >> strip_tac >> metis_tac[]) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  qexistsl_tac [`inst2`,`t1 with vs_inst_idx := SUC t.vs_inst_idx`,
                `fn'`,`bb'`,`B1`,`sites1`,`X`] >> simp[] >>
  `!m. step_inst m C' inst t = OK t1` by
    (qpat_x_assum `step_inst fuel C' inst t = OK t1` mp_tac >>
     asm_simp_tac bool_ss [step_inst_non_invoke]) >>
  gen_tac >> CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >>
  pure_asm_rewrite_tac [optionTheory.option_case_def] >>
  BETA_TAC >>
  pure_asm_rewrite_tac [exec_result_case_def, COND_CLAUSES] >>
  BETA_TAC >> REFL_TAC
QED

Theorem ld_joint_noncall_continue:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 tnext fn' bb' B1 sites1 X1.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!m. exec_block m C' bb' t = exec_block m C' bb' tnext) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) tnext
      n a U B1 HP (occurrence_step a HP H inst s1) sites1 X1 ts
Proof
  rpt gen_tac >> strip_tac >>
  `mem_inv dload_offset_ok C vs /\ mem_inv dload_headroom_ok C vs` by
    fs[o1_src_inv_def] >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn /\ fn_inst_wf fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- (drule_all ld_joint_dload_next >> strip_tac >>
      `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es` by
        (irule ld_joint_generated_slice >> simp[] >> metis_tac[]) >>
      `!m. exec_block m C' bb' t =
          exec_block m C' bb' (t4 with vs_inst_idx := t.vs_inst_idx+4)` by
        (gen_tac >> irule ld_four_step_packet_continuation >>
         simp[EL] >> qexistsl_tac [`t1`,`t2`,`t3`] >>
         `!j. j < LENGTH es ==> (EL j es).inst_opcode <> INVOKE` by
           (rpt strip_tac >>
            `MEM (EL j es) es` by metis_tac[MEM_EL] >>
            fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
         `(HD es).inst_opcode <> INVOKE /\
          (EL 1 es).inst_opcode <> INVOKE /\
          (EL 2 es).inst_opcode <> INVOKE /\
          (EL 3 es).inst_opcode <> INVOKE` by
           (conj_tac
            >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
            rpt conj_tac >> first_x_assum irule >> simp[]) >>
         fs[step_inst_non_invoke]) >>
      `active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
        (drule ld_joint_source >>
         disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_projection) >>
         fs[Once frame_reachable_cases] >> metis_tac[]) >>
      qexistsl_tac [`inst2`,`t4 with vs_inst_idx := t.vs_inst_idx+4`,
                    `fn'`,`bb'`,`B`,`sites`,`X1`] >> simp[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (drule_all ld_joint_dloadbytes_next >> strip_tac >>
      `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es` by
        (irule ld_joint_generated_slice >> simp[] >> metis_tac[]) >>
      `!m. exec_block m C' bb' t =
          exec_block m C' bb' (t3 with vs_inst_idx := t.vs_inst_idx+2)` by
        (gen_tac >> irule ld_two_step_packet_continuation >>
         simp[] >> qexists_tac `t2` >>
         `(HD es).inst_opcode <> INVOKE /\ (EL 1 es).inst_opcode <> INVOKE` by
           (`MEM (HD es) es /\ MEM (EL 1 es) es` by
              (conj_tac >- (Cases_on `es` >> gvs[]) >>
               simp[MEM_EL] >> qexists_tac `1` >> simp[]) >>
            fs[EVERY_MEM] >>
            qpat_assum `!i. MEM i es ==> _` (qspec_then `HD es` mp_tac) >>
            qpat_x_assum `!i. MEM i es ==> _` (qspec_then `EL 1 es` mp_tac) >>
            simp[] >> rpt strip_tac >> gvs[]) >>
         fs[step_inst_non_invoke]) >>
      `active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
        (drule ld_joint_source >>
         disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_projection) >>
         fs[Once frame_reachable_cases] >> metis_tac[]) >>
      qexistsl_tac [`inst2`,`t3 with vs_inst_idx := t.vs_inst_idx+2`,
                    `fn'`,`bb'`,`B`,`sites`,`X`] >> simp[]) >>
  drule_all ld_joint_singleton_continue >> metis_tac[]
QED

