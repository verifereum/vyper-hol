(*
 * Paired-prefix extension for the N10 opcode family (CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY).
 *)
Theory concretizePtrBufferCopyFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrBufferCopyContent
  concretizePtrOpaqueRetpc ptrDiscipline memLocDefs list pointerConfinedDefs
  concretizePtrRequestHistory venomExecSemantics venomState venomInst words codegenRel

Theorem ptr_buffer_copy_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  inst.inst_operands = [dop;sop;nop] ==>
  EVERY (ptr_nonopaque_operand fn) [dop;sop;nop] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [sop;nop]
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) [dop;sop;nop]` by
    (`EVERY (ptr_nonopaque_operand fn) inst.inst_operands` suffices_by simp[] >>
     irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  simp[] >>
  `!v. (sop = Var v \/ nop = Var v) ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!v'. _` (qspec_then `v` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `dop = Var v` >> gvs[] >>
     Cases_on `sop = Var v` >> gvs[] >>
     Cases_on `nop = Var v` >> gvs[]) >>
  `op_taint tn sop = {} /\ op_taint tn nop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
     simp[taint_ok_def] >> metis_tac[]) >>
  simp[] >> conj_tac >> Cases_on `sop` >> Cases_on `nop` >>
  simp[op_prov_def] >> rpt conj_tac >>
  qmatch_goalsub_rename_tac `FLOOKUP TG v` >>
  Cases_on `FLOOKUP TG v` >> gvs[] >> metis_tac[]
QED

Theorem ptr_buffer_copy_execution[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  inst.inst_operands = [dop;sop;nop] /\
  IS_SOME (eval_operand dop s) = IS_SOME (eval_operand dop t) /\
  eval_operand sop s = eval_operand sop t /\
  eval_operand nop s = eval_operand nop t /\
  step_inst fuel Ct inst t = OK t' ==>
  ?d dt r n s'.
    eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
    eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
    eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
    step_inst 0 C inst s = OK s' /\
    (inst.inst_opcode = RETURNDATACOPY ==>
      w2n r + w2n n <= LENGTH s.vs_returndata) /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata` by
    metis_tac[ptr_history_content_call_ctx, ptr_history_content_code,
      ptr_history_content_data_section, ptr_history_content_returndata] >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM]) >>
  `step_inst_base inst t = OK t'` by
    metis_tac[step_inst_non_invoke] >>
  `?d dt r n. eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
    eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
    eval_operand nop s = SOME n /\ eval_operand nop t = SOME n` by
    (qpat_x_assum `step_inst_base inst t = OK t'` mp_tac >>
     fs[MEM] >> PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[Once opcode_case_def, AllCaseEqs()] >>
     Cases_on `eval_operand dop s` >> gvs[] >> metis_tac[]) >>
  `inst.inst_opcode = RETURNDATACOPY ==>
    w2n r + w2n n <= LENGTH s.vs_returndata` by
    (strip_tac >> drule_all ptr_returndatacopy_success_bound >> simp[]) >>
  `?s' tt. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK tt /\
    (!i. i < w2n n ==> read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) tt.vs_memory)` by
    (`s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata` by simp[] >>
     fs[MEM]
     >- (drule_all ptr_calldatacopy_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM])
     >- (drule_all ptr_codecopy_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM])
     >- (drule_all ptr_dloadbytes_content >> strip_tac >> gvs[] >>
         goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM]) >>
     `w2n r + w2n n <= LENGTH s.vs_returndata` by gvs[] >>
     drule_all ptr_returndatacopy_content >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM]) >>
  gvs[] >> qexists_tac `s'` >> simp[] >>
  fs[MEM] >> simp[step_inst_non_invoke]
QED

Theorem ptr_buffer_copy_post_memory[local]:
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  step_inst fuel C inst s = OK s' ==>
  s' = s with vs_memory := s'.vs_memory
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  fs[MEM] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def, AllCaseEqs()] >>
  strip_tac >> gvs[write_memory_with_expansion_def]
QED

Theorem ptr_buffer_copy_history_content[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  step_inst fuel C inst s = OK s' /\ step_inst fuelt Ct inst t = OK t' ==>
  ptr_history_content (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s' = s with vs_memory := s'.vs_memory` by
    (irule ptr_buffer_copy_post_memory >> rpt (goal_assum (drule_at Any))) >>
  `t' = t with vs_memory := t'.vs_memory` by
    (irule ptr_buffer_copy_post_memory >> rpt (goal_assum (drule_at Any))) >>
  once_asm_rewrite_tac[] >> simp[] >>
  irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
  fs[MEM] >> simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem ptr_paired_buffer_copy_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
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
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  cheat
QED

