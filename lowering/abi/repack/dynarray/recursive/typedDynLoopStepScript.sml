(* TOP-LEVEL: a verified element-copy step advances the complete memory,
   control and operand invariant. The counter, header and modified names
   are parameters, so this lemma also applies to fixed-array copy loops. *)
Theory typedDynLoopStep
Ancestors
  typedCopyStateFrame
  typedDynLoopInvariant typedSArrayDynInvariant typedArrayCopyMemory
  memoryValueDefs valueEncoding compileEnv venomState venomInst list words arithmetic

Theorem array_copy_loop_inv_step:
  !counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current out.
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current /\
    copy_state_frame current out /\
    i < copy_count /\ (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (!j. j < i ==> val_wf ftv (at_index j)) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    out.vs_current_bb = cond_label /\ out.vs_inst_idx = 0 /\ ~out.vs_halted /\
    eval_operand (Var counter) out = SOME (n2w (SUC i)) /\
    memory_value_rel ftv (at_index i) (w2n dst_data + i * type_memory_size ftv) out.vs_memory /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset current.vs_memory /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= w2n dst_data + i * type_memory_size ftv \/
        w2n dst_data + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset out.vs_memory) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) modified_names ==>
      eval_operand arg_op out = eval_operand arg_op current) ==>
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial (SUC i) out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
    initial.vs_memory i current.vs_memory` by
    (qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [array_copy_loop_inv_def] >> simp[]) >>
  mp_tac (Q.SPECL [`ftv`, `atv`, `at_index`, `copy_count`, `i`, `w2n (src_data:bytes32)`, `w2n (dst_data:bytes32)`,
    `initial.vs_memory`, `current.vs_memory`, `out.vs_memory`] array_copy_memory_inv_step) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`counter`, `cond_label`, `modified_names`, `ftv`, `atv`, `at_index`, `copy_count`,
    `src_data`, `dst_data`, `initial`, `i`, `current`, `out`] array_copy_loop_inv_advance) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED
