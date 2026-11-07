(*
 * Paired-prefix extension for the N15 opcode family (CALL; STATICCALL).
 *)
Theory concretizePtrCallFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrMloadRecovery
  concretizePtrRequestCompletionProbe copyFwdEquiv
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory ptrDiscipline
  list venomState contextCodegenRel codegenRel allocaRemapDefs
  pointerConfinedDefs memLocDefs concretizePtrOpaqueRetpc
  concretizePtrReturnTransport concretizePtrValueTransport finite_map pred_set

Theorem ptr_call_scalar_not_pointer[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((inst.inst_opcode = CALL /\ pre = [gas; addr; value]) \/
   (inst.inst_opcode = STATICCALL /\ pre = [gas; addr])) /\
  inst.inst_operands = pre ++ [aop; azop; rop; rzop] /\
  MEM (Var v) (pre ++ [azop; rzop]) ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >> strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  fs[ptr_use_ok_def] >>
  qpat_x_assum `!v. _ ==> _` (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def,
       Excl "FILTER"] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  fs[MEM] >> gvs[] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_call_operand_transport:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  ((inst.inst_opcode = CALL /\ pre = [gas; addr; value]) \/
   (inst.inst_opcode = STATICCALL /\ pre = [gas; addr])) /\
  inst.inst_operands = pre ++ [aop; azop; rop; rzop] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels ==>
  (!op. MEM op inst.inst_operands ==>
    op_taint tn op = {} /\
    ptr_lookup_transport births positions (op_prov TG op) {}
      (eval_operand op s) (eval_operand op t)) /\
  eval_operands (pre ++ [azop; rzop]) s = eval_operands (pre ++ [azop; rzop]) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[] >>
      drule ptr_mixed_vars_eval >> simp[EVERY_MEM] >>
      disch_then (qspec_then `op` mp_tac) >> fs[EVERY_MEM]) >>
  `EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
      op_taint tn op = {}) (pre ++ [azop; rzop])` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     `MEM op inst.inst_operands` by (gvs[] >> fs[MEM]) >>
     `ptr_nonopaque_operand fn op /\ op_taint tn op = {}` by fs[EVERY_MEM] >>
     simp[] >> Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >>
     metis_tac[ptr_call_scalar_not_pointer]) >>
  drule_all ptr_mixed_scalar_operands_equal >> simp[]
QED

Theorem ptr_paired_call_input_bytes:
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  read_memory (w2n x) n a.po_state = read_memory (w2n y) n at.po_state
Proof
  strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >> strip_tac >>
     drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!j. j < n ==> w2n x + j NOTIN a.po_taint.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x + j /\ w2n x + j < w2n x + n` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     fs[MEM] >> simp[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl_tac [`w2n x`, `n`, `w2n x + j`] >> simp[]) >>
  `!j. j < n ==> read_byte (w2n x + j) a.po_state.vs_memory =
     read_byte (w2n y + j) at.po_state.vs_memory` by
    (`a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
     drule ptr_paired_read_range_masked_bytes >>
     simp[] >> gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule LIST_EQ >> simp[read_memory_def, LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[take_drop_replicate_el, GSYM read_byte_def, mem_byte_at_def]
QED

Theorem ptr_paired_call_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] ==>
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

