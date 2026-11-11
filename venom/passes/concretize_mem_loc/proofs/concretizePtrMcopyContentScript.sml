Theory concretizePtrMcopyContent
Ancestors concretizePtrMcopyEndpoint concretizePtrMloadRecovery concretizePtrCopyContent
  concretizePtrPairedPrefix ptrDiscipline o1PassContract unitShapeDefs
  stackPlanGen stackPlanTypes venomWf cfgWf o1ScheduleDecomp unitMemInv
  contextCodegenRel memLocDefs concretizeMemLocDefs venomExecSemantics venomState words list

Theorem ptr_paired_mcopy_postwrite_bytes:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?dop sop nop d r dt rt n.
    a.po_inst.inst_operands = [dop;sop;nop] /\ at.po_inst = a.po_inst /\
    eval_operand dop a.po_state = SOME d /\
    eval_operand sop a.po_state = SOME r /\
    eval_operand nop a.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    (!fuel ctx. step_inst fuel ctx a.po_inst a.po_state =
      OK (mcopy (w2n d) (w2n r) (w2n n) a.po_state)) /\
    (!post postt. step_inst_base a.po_inst a.po_state = OK post /\
      step_inst_base at.po_inst at.po_state = OK postt ==>
      !j. j < w2n n /\ w2n d+j NOTIN mem_taint a.po_taint a.po_inst a.po_state post ==>
        read_byte (w2n d+j) post.vs_memory = read_byte (w2n dt+j) postt.vs_memory)
Proof
  strip_tac >> drule_all ptr_paired_mcopy_endpoint_inputs >> strip_tac >>
  `!j. j < w2n n /\ w2n r+j NOTIN a.po_taint.t_mem ==>
     read_byte (w2n r+j) a.po_state.vs_memory =
     read_byte (w2n rt+j) at.po_state.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule (Q.INST [`ops` |-> `<|iao_ofst := sop; iao_size := SOME nop; iao_max_size := SOME nop|>`]
       (SPEC_ALL ptr_paired_read_range_masked_bytes) |> SIMP_RULE (srw_ss()) []) >>
     simp[mem_read_ops_def, inst_read_op_def] >>
     conj_tac >- (qexists `w2n n` >> simp[]) >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "content"
QED

Resume ptr_paired_mcopy_postwrite_bytes[content]:
  `?post postt. step_inst_base a.po_inst a.po_state = OK post /\
    step_inst_base a.po_inst at.po_state = OK postt /\
    (!j. j < w2n n /\ w2n d+j NOTIN mem_taint a.po_taint a.po_inst a.po_state post ==>
      read_byte (w2n d+j) post.vs_memory = read_byte (w2n dt+j) postt.vs_memory)` by
    (irule ptr_mcopy_masked_content >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`dop`,`sop`,`nop`,`d`,`r`,`dt`,`rt`,`n`] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Finalise ptr_paired_mcopy_postwrite_bytes
