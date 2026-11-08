Theory concretizePtrDeletedGaps
Ancestors concretizePtrLayoutOutput concretizePtrLedgerAlignment
  concretizeMemLocDefs staticLayoutCompletionProofs staticLayoutAllocatorProofs
  venomExecSemantics passSharedDefs removeUnusedSsaProofs list finite_map

Theorem ptr_positioned_nop_iff:
  MEM i (fn_insts fn) /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) ==>
  ((concretize_inst_with_positions positions i).inst_opcode = NOP <=>
   i.inst_opcode = NOP)
Proof
  strip_tac >> Cases_on `i.inst_opcode = ALLOCA`
  >- (`?p. FLOOKUP positions (Allocation i.inst_id) = SOME p` by metis_tac[] >>
      simp[concretize_inst_with_positions_def] >>
      Cases_on `i.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[mk_assign_inst_def]) >>
  simp[concretize_inst_with_positions_def]
QED

Theorem ptr_fresh_layout_total:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  ?layout. fn' = apply_context_concretize_layout ctx layout fn /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
      ?p. FLOOKUP layout.cl_positions (Allocation i.inst_id) = SOME p) /\
    (!i. MEM i (fn_insts fn) ==>
      ((concretize_inst_with_positions layout.cl_positions i).inst_opcode = NOP <=>
       i.inst_opcode = NOP))
Proof
  strip_tac >> drule_all ptr_fresh_layout_representation >> strip_tac >>
  qexists_tac `layout` >> simp[] >>
  `!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout.cl_positions (Allocation i.inst_id) = SOME p` by
    (rpt strip_tac >>
     drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
     Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []` >>
     gvs[] >>
     `layout.cl_positions = completed` by metis_tac[ptr_mk_layout_positions] >>
     gvs[]
     >- (drule_all (cj 2 complete_alloc_positions_with_imports_success) >> metis_tac[]) >>
     drule (cj 2 complete_alloc_positions_success) >> metis_tac[]) >>
  metis_tac[ptr_positioned_nop_iff]
QED

Theorem ptr_positioned_block_nop_iff:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) /\
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions ==>
  ((concretize_inst_with_positions positions (EL i bb.bb_instructions)).inst_opcode = NOP <=>
   (EL i bb.bb_instructions).inst_opcode = NOP)
Proof
  strip_tac >> irule ptr_positioned_nop_iff >>
  qexists_tac `fn` >> simp[] >>
  simp[venomInstTheory.fn_insts_def, fn_insts_blocks_flat,
    MEM_FLAT, MEM_MAP] >>
  qexists_tac `bb.bb_instructions` >> simp[EL_MEM] >> metis_tac[]
QED

Theorem ptr_ledger_source_gap:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) /\
  MEM bb fn.fn_blocks /\
  ptr_ledger_block_alignment positions bb.bb_instructions tgt indices /\
  j < LENGTH indices /\ i < EL j indices /\
  (j = 0 \/ EL (j-1) indices < i) ==>
  (EL i bb.bb_instructions).inst_opcode = NOP
Proof
  strip_tac >>
  `i < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     `EL j indices < LENGTH bb.bb_instructions` by metis_tac[] >> decide_tac) >>
  drule_all ptr_positioned_block_nop_iff >>
  metis_tac[ptr_ledger_alignment_gap]
QED

Theorem ptr_ledger_source_tail:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) /\
  MEM bb fn.fn_blocks /\
  ptr_ledger_block_alignment positions bb.bb_instructions tgt indices /\
  i < LENGTH bb.bb_instructions /\ (indices = [] \/ LAST indices < i) ==>
  (EL i bb.bb_instructions).inst_opcode = NOP
Proof
  strip_tac >> drule_all ptr_positioned_block_nop_iff >>
  metis_tac[ptr_ledger_alignment_tail]
QED

