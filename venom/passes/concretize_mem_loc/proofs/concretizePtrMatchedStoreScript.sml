Theory concretizePtrMatchedStore
Ancestors
  concretizePtrBytes concretizePtrStoreSteps concretizePtrPrefixLedger concretizePtrLedgerProbe
  concretizePtrChronologicalHistory ptrDiscipline venomExecSemantics venomState venomInst codegenRel pred_set arithmetic

Theorem ptr_mstore_matched:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME x /\ eval_operand sv s = SOME v /\
  eval_operand ta t = SOME y /\ eval_operand tv t = SOME vt /\
  word_agree_except (op_taint tn sv) v vt /\
  (!i:num. reloc i = w2n y + (i - w2n x)) ==>
  ?post postt.
    step_inst fuel C si s = OK post /\
    step_inst fuel Ct ti t = OK postt /\
    (!i. i IN range_bytes (step_writes si s post) ==>
      reloc i IN range_bytes (step_writes ti t postt)) /\
    ptr_bytes_agree
      (range_bytes (step_writes si s post) DIFF
        (step_taint si s post tn).t_mem)
      reloc post.vs_memory postt.vs_memory
Proof
  rpt strip_tac >>
  qexistsl_tac [`mstore (w2n x) v s`, `mstore (w2n y) vt t`] >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  simp[step_writes_def, source_memory_write_ranges_def,
    fixed_source_write_range_def, range_bytes_def] >>
  simp[ptr_bytes_agree_def, step_taint_def, mem_taint_def,
    written_taint_def] >>
  rpt strip_tac >>
  `i = w2n x + (i - w2n x)` by decide_tac >>
  `i + w2n y - w2n x = w2n y + (i - w2n x)` by decide_tac >>
  `i - w2n x < 32 /\ i - w2n x NOTIN op_taint tn sv` by
    (conj_tac >- decide_tac >> metis_tac[ADD_COMM]) >>
  `EL (i - w2n x) (word_to_bytes v T) =
    EL (i - w2n x) (word_to_bytes vt T)` by
    metis_tac[word_agree_except_def] >>
  metis_tac[ptr_mstore_written_bytes]
QED

Theorem ptr_mstore_matched_events:
  a.po_inst.inst_opcode = MSTORE /\ b.po_inst.inst_opcode = MSTORE /\
  a.po_inst.inst_operands = [sa;sv] /\ b.po_inst.inst_operands = [ta;tv] /\
  eval_operand sa a.po_state = SOME x /\
  eval_operand sv a.po_state = SOME v /\
  eval_operand ta b.po_state = SOME y /\
  eval_operand tv b.po_state = SOME vt /\
  word_agree_except (op_taint a.po_taint sv) v vt /\
  (!i:num. reloc i = w2n y + (i - w2n x)) /\
  active_inst a.po_fn a.po_inst a.po_state /\
  active_inst b.po_fn b.po_inst b.po_state /\
  active_inst a.po_fn ni
    (mstore (w2n x) v a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
  active_inst b.po_fn nit
    (mstore (w2n y) vt b.po_state with vs_inst_idx := SUC b.po_state.vs_inst_idx) ==>
  ?z w. z = ptr_ledger_next a ni (mstore (w2n x) v a.po_state) /\
    w = ptr_ledger_next b nit (mstore (w2n y) vt b.po_state) /\
    ptr_ledger_write_pair C Ct reloc a z b w
Proof
  rpt strip_tac >>
  drule_all ptr_mstore_matched >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  `ptr_chrono_step C a (ptr_ledger_next a ni (mstore (w2n x) v a.po_state))` by
    (irule ptr_ledger_next_step >>
     simp[is_terminator_def, step_inst_non_invoke, step_inst_base_def,
       exec_write2_def] >> qexists_tac `0` >> simp[]) >>
  `ptr_chrono_step Ct b (ptr_ledger_next b nit (mstore (w2n y) vt b.po_state))` by
    (irule ptr_ledger_next_step >>
     simp[is_terminator_def, step_inst_non_invoke, step_inst_base_def,
       exec_write2_def] >> qexists_tac `0` >> simp[]) >>
  gvs[step_writes_def] >>
  simp[ptr_ledger_write_pair_def, ptr_ledger_next_def, ptr_observe_def,
    step_writes_def, is_terminator_def]
QED
