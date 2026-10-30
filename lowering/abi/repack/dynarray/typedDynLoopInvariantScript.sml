(* TOP-LEVEL: a reusable array-copy loop invariant with the actual counter
   and generated-name range supplied by its compiler. Element sizes may
   differ or be zero, and a child may allocate an arbitrary number of names. *)
Theory typedDynLoopInvariant
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame typedDynLoopNames typedArrayLoopAddress typedArrayCopyMemory typedSArrayDynInvariant
  memoryValueDefs valueEncoding compileEnv venomState venomInst fragBlockPath list words arithmetic

Definition array_copy_loop_inv_def:
  array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count
      (src_data:bytes32) (dst_data:bytes32) initial i current <=>
    current.vs_current_bb = cond_label /\ current.vs_inst_idx = 0 /\ ~current.vs_halted /\
    copy_state_frame initial current /\
    eval_operand (Var counter) current = SOME (n2w i) /\
    array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
      initial.vs_memory i current.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name) modified_names ==>
      eval_operand arg_op current = eval_operand arg_op initial)
End

Theorem array_copy_loop_inv_operand:
  !counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current arg_op.
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current /\
    EVERY (\name. arg_op <> Var name) modified_names ==>
    eval_operand arg_op current = eval_operand arg_op initial
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_loop_inv_def] >> strip_tac >>
  qpat_x_assum `!arg_op. _` (qspec_then `arg_op` mp_tac) >> simp[]
QED

Theorem array_copy_loop_inv_advance:
  !counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current out.
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current /\
    copy_state_frame current out /\
    out.vs_current_bb = cond_label /\ out.vs_inst_idx = 0 /\ ~out.vs_halted /\
    eval_operand (Var counter) out = SOME (n2w (SUC i)) /\
    array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
      initial.vs_memory (SUC i) out.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name) modified_names ==>
      eval_operand arg_op out = eval_operand arg_op current) ==>
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial (SUC i) out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_loop_inv_def] >> strip_tac >>
  mp_tac (Q.SPECL [`modified_names`, `initial`, `current`, `out`] compiler_operands_frame_trans) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `copy_state_frame initial out` by
    (irule copy_state_frame_trans >> qexists_tac `current` >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem array_copy_element_pointer_fit:
  !(data:bytes32) copy_count i stride.
    i < copy_count /\ w2n data + copy_count * stride < dimword(:256) ==>
    w2n (data + n2w i * n2w stride) = w2n data + i * stride /\
    w2n (data + n2w i * n2w stride) + stride < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`w2n (data:bytes32)`, `i`, `copy_count`, `stride`] array_copy_element_window) >>
  impl_tac >- simp[] >> strip_tac >>
  `w2n data + i * stride < dimword(:256)` by decide_tac >>
  `w2n (data + n2w i * n2w stride) = w2n data + i * stride` by
    (irule typed_array_loop_address_natural >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED
