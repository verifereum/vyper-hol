(* Static fetch ranges of a saved storage/transient operand's restore. *)
Theory entryCreateRestoreGeometry
Ancestors
  exprPtrUnwrapEnsureShape abiBufferAllocationCode copyExecution
  abiEncoderChildCode abiEncoderProps emitHelperProps emitHelper compileEnv
  arithmetic list

(* Both ABI row shapes reach their restore after an address ADD. *)
Theorem restore_after_head_room:
  ((?out. emit_op ADD args a = (out,su)) \/
    (?dst h cursor ops. abi_encode_child_prefix dst h cursor a = (ops,su))) ==>
  0 < LENGTH su.cs_current_insts
Proof
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (drule emitted_insts_emit_op >> simp[]) >>
  pop_assum mp_tac >>
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >> drule emitted_insts_emit_op >> simp[]
QED

Theorem slot_restore_fetch_geometry:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm su = (op,sb) /\
  compile_alloc_buffer nb su = (buf,sm) /\
  (su.cs_current_bb <> sb.cs_current_bb \/ 0 < LENGTH su.cs_current_insts) ==>
  (!j. j < 3 ==>
    su.cs_next_id + j IN frag_ids su sb /\
    (su.cs_current_bb <> sb.cs_current_bb \/
      LENGTH su.cs_current_insts + j <> LENGTH sb.cs_current_insts)) /\
  (!j. j < 2 ==>
    sm.cs_next_id + j IN frag_ids su sb /\
    (sm.cs_current_bb <> sb.cs_current_bb \/
      LENGTH sm.cs_current_insts + j <> LENGTH sb.cs_current_insts)) /\
  (n <> 1 ==>
    (!j. j < 2 ==>
      sm.cs_next_id + 2 + j IN frag_ids su sb /\
      (slot_copy_cond sm <> sb.cs_current_bb \/ j <> LENGTH sb.cs_current_insts)) /\
    (!j. j < 8 ==>
      sm.cs_next_id + 4 + j IN frag_ids su sb /\
      (slot_copy_body sm <> sb.cs_current_bb \/ j <> LENGTH sb.cs_current_insts)))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  `sm.cs_current_bb = su.cs_current_bb /\
   LENGTH sm.cs_current_insts = LENGTH su.cs_current_insts + 1 /\
   sm.cs_next_id = su.cs_next_id + 1` by
    (drule compile_alloc_buffer_code >> simp[GSYM AND_IMP_INTRO] >>
     strip_tac >> simp[]) >>
  Cases_on `n = 1`
  >- (`LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts + 2 /\
       sb.cs_next_id = sm.cs_next_id + 2` by
      (qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
       qpat_x_assum `(comp_bind _ _) _ = _` mp_tac >>
       simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
       drule emitted_insts_emit_op >> drule emitted_insts_emit_void >> simp[]) >>
      rpt strip_tac >> fs[frag_ids_def] >> decide_tac) >>
  qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  qpat_x_assum `sb = slot_copy_final _ _ _ _ _` kall_tac >>
  `slot_copy_cond sm <> sb.cs_current_bb /\ slot_copy_body sm <> sb.cs_current_bb` by
    (simp[slot_copy_cond_def,slot_copy_body_def,slot_copy_exit_def] >>
     conj_tac >> strip_tac >> drule fresh_label_output_inj >> simp[]) >>
  qpat_assum `sb.cs_current_insts = []` (fn th => pure_rewrite_tac[th,LENGTH]) >>
  rpt strip_tac >> fs[frag_ids_def] >> decide_tac
QED
