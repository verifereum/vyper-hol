(*
 * Paired-prefix extension for the N14 opcode family (SHA3; LOG).
 *)
Theory concretizePtrHashLogFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrMloadRecovery
  regularMemorySim memSafeRun ptrDiscipline contextCodegenRel
  venomInst venomWf venomExecProofs unitLabelMapIdentity list
  pointerConfinedDefs memLocDefs finite_map pred_set
  concretizePtrReturnTransport concretizePtrOpaqueRetpc

Theorem ptr_hash_log_nonrevert[local]:
  active_inst fn inst s /\ ALL_DISTINCT (fn_labels fn) /\
  MEM inst.inst_opcode [SHA3; LOG] ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >> reverse conj_tac
  >- (fs[MEM] >> simp[about_to_revert_def]) >>
  qpat_x_assum `active_inst fn inst s` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    simp[get_instruction_def] >>
  simp[in_revert_forward_def] >> strip_tac >>
  drule_all revert_forward_at_opcode >> fs[MEM]
QED

Theorem ptr_hash_log_read_untainted[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [SHA3; LOG] /\
  MEM (off,n) (source_memory_read_ranges inst s) ==>
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  (!j. j < n ==> off+j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~about_to_revert fn inst s` by (fs[MEM] >> simp[about_to_revert_def]) >>
  conj_tac
  >- (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  fs[MEM] >> gvs[taint_ok_def] >>
  qpat_x_assum `!off' len i. _`
    (qspecl_then [`off`,`n`,`off+j`] mp_tac) >> simp[]
QED

Theorem ptr_log_read_descriptor[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topics ==>
  mem_write_ops inst = NONE /\
  mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME szop;
                            iao_max_size := SOME szop|>
Proof
  strip_tac >> simp[mem_write_ops_def, mem_read_ops_def] >>
  Cases_on `topics` >> simp[]
QED

Theorem ptr_log_scalar_vars[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::szop::topics ==>
  !v. MEM (Var v) (szop::topics) ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  drule_all ptr_log_read_descriptor >> strip_tac >>
  gen_tac >> strip_tac >> spose_not_then assume_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `MEM (Var v) inst.inst_operands` by
    (simp[] >> metis_tac[MEM_REVERSE, MEM]) >>
  `FILTER ($= (Var v)) inst.inst_operands = [Var v] /\ addr = Var v` by
    (qpat_x_assum `ptr_use_ok P _ inst` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def] >>
     disch_then (qspec_then `v` mp_tac) >>
     `MEM (Var v) rest` by (qpat_x_assum `MEM (Var v) inst.inst_operands` mp_tac >> simp[]) >> simp[]) >>
  `REVERSE inst.inst_operands = Var v::szop::topics ++ [Lit tc]` by
    simp[REVERSE_APPEND] >>
  `FILTER ($= (Var v)) (REVERSE inst.inst_operands) = [Var v]` by
    simp[FILTER_REVERSE] >>
  qpat_x_assum `FILTER _ (REVERSE inst.inst_operands) = _` mp_tac >>
  simp[FILTER_APPEND_DISTRIB] >>
  Cases_on `szop = Var v` >> simp[] >>
  fs[MEM, FILTER_EQ_NIL, EXISTS_MEM]
QED

Theorem ptr_paired_hash_log_payload[local]:
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
  active_inst a.po_fn a.po_inst a.po_state /\
  ALL_DISTINCT (fn_labels a.po_fn) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  MEM a.po_inst.inst_opcode [SHA3; LOG] /\
  mem_read_ops a.po_inst = SOME ops /\
  inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
    (SOME x) (SOME y) ==>
  TAKE n (DROP (w2n x) a.po_state.vs_memory ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n y) at.po_state.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >>
  `~in_revert_forward a.po_fn a.po_state` by
    (drule_all ptr_hash_log_nonrevert >> simp[]) >>
  `!j. j < n ==> w2n x+j NOTIN a.po_taint.t_mem` by
    (drule_all ptr_hash_log_read_untainted >> simp[]) >>
  `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  drule ptr_paired_read_range_masked_bytes >>
  simp[] >> strip_tac >>
  simp[venom_returndata_read_byte] >> irule GENLIST_CONG >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ptr_paired_hash_log_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [SHA3; LOG] ==>
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

