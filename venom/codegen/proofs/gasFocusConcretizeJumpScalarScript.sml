Theory gasFocusConcretizeJumpScalar
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrDeletedGapHistory
  concretizePtrOpaqueRetpc concretizePtrParamSupport
  concretizePtrChronologicalHistory ptrDiscipline contextCodegenRel
  unitLabelMapIdentity pointerConfinedDefs memLocDefs finite_map list

(* Current taint safety and tagged support suffice at the selected operand. *)
Theorem ptr_focus_jump_scalar:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  opaque_use_ok a.po_fn /\ MEM a.po_inst.inst_opcode [JNZ; DJMP] /\
  MEM cond a.po_inst.inst_operands ==>
  ptr_nonopaque_operand a.po_fn cond /\ op_prov TG cond = NONE /\
  op_taint a.po_taint cond = {}
Proof
  strip_tac >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM, MEM_EL]) >>
  `fn_ptr_ok P a.po_fn` by
    (qpat_x_assum `EVERY (fn_ptr_ok _) _` mp_tac >> simp[EVERY_MEM]) >>
  (conj_tac
   >- (`~MEM a.po_inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by fs[MEM] >>
       drule_all ptr_nonopaque_instruction_operands >> simp[EVERY_MEM])) >>
  (reverse conj_tac
   >- (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[])) >>
  Cases_on `cond` >> simp[op_prov_def] >>
  rename1 `FLOOKUP TG v = NONE` >>
  Cases_on `FLOOKUP TG v` >> simp[] >>
  `v IN fn_pv P a.po_fn` by metis_tac[ptr_static_support_def] >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  fs[MEM] >> gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_write_ops_def, mem_read_ops_def] >> metis_tac[]
QED
