Theory gasFocusConcretizeInvokeRestrictions
Ancestors
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrSourceOwnership concretizePtrOpaqueRetpc
  ptrDiscipline venomExecSemantics venomExecProofs venomWf venomState
  venomInst list contextCodegenRel unitLabelMapIdentity

(* Only the selected instruction needs taint safety: ownership supplies its
   actual reachability, not a whole-history discipline premise. *)
Theorem ptr_focus_invoke_restrictions:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  decode_invoke a.po_inst = SOME (nm,ops) ==>
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {}
Proof
  strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >>
     metis_tac[lookup_block_MEM, MEM_EL]) >>
  `a.po_inst.inst_operands = Label nm :: ops` by
    (gvs[decode_invoke_def, AllCaseEqs()]) >>
  conj_tac
  >- (`~MEM a.po_inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by simp[] >>
      drule_all ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint a.po_taint op = {}) ops` by
    (gvs[EVERY_MEM, taint_ok_def] >> metis_tac[]) >>
  pop_assum mp_tac >>
  qpat_x_assum `decode_invoke _ = _` kall_tac >>
  qpat_x_assum `a.po_inst.inst_operands = _` kall_tac >>
  Induct_on `ops` >> simp[]
QED
