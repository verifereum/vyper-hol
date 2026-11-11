Theory concretizePtrContextRoot
Ancestors
  concretizePtrPairedRoot concretizePtrStagePairedBridge
  concretizePtrDeletedGapHistory concretizePtrPairedFields
  o1PassLift o1PassContract unitTransformDefs venomWf venomInst
  list finite_map

Theorem ptr_paired_context_root:
  C.ctx_entry = Ct.ctx_entry /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\ vs.vs_vars = FEMPTY /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_chrono_history vs Ct [at] at /\ at.po_stack = [] ==>
  ?h a tokens registry births PT TG saved entries H.
    ptr_paired_prefix R lp positions lo vs C Ct
      h a [at] at [] tokens registry births PT TG saved entries H [] [] /\
    a.po_inst.inst_opcode <> NOP /\
    at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst
Proof
  strip_tac >> drule ptr_chrono_root_inversion >> strip_tac >>
  drule_all list_rel_lookup_function >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >> strip_tac >>
  `MEM x C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `MEM at.po_fn Ct.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `first_block_no_phi x /\ fn_inst_wf x /\
    EVERY bb_well_formed x.fn_blocks /\
    (!i. MEM i (fn_insts x) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp x) (Allocation i.inst_id)))` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `x.fn_blocks <> []` by
    (fs[ptr_paired_code_def] >>
     Cases_on `x.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `(HD x.fn_blocks).bb_instructions <> []` by
    (Cases_on `x.fn_blocks` >> gvs[bb_well_formed_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by fs[EVERY_MEM] >>
  `C.ctx_entry = SOME name` by metis_tac[] >>
  drule_all ptr_paired_root_normalized >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[ptr_gap_scan_fields]
QED
