(* Compiler emission wrappers for uniform checked paths. Generic EVERY
   closure is already abi_decoder_emitted_every_append; do not duplicate it. *)
Theory emittedSeqComposePtr
Ancestors instSeqComposePtr exprLoweringProps emitHelperProps contextCodegenRel
  ptrDiscipline stateFrame venomState venomInst compileEnv list

Theorem emitted_inst_seq_ptr_uniform_compose:
  inst_extends a b /\ inst_extends b c /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  run_inst_seq (emitted_insts a b) s = OK t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts a b)
         (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 (emitted_insts b c)
         (t with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts a c)
         (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac[] >> irule inst_seq_ptr_uniform_append >>
  metis_tac[]
QED

Theorem emitted_inst_seq_ptr_uniform_abort_extend:
  inst_extends a b /\ inst_extends b c /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  run_inst_seq (emitted_insts a b) s = Abort ex t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts a b)
         (s with vs_inst_idx := k) G1 tn1) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts a c)
         (s with vs_inst_idx := k) G1 tn1
Proof
  strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac[] >> irule inst_seq_ptr_uniform_abort_append >>
  metis_tac[]
QED

Theorem emitted_op_nonterminators:
  emit_op opc ops st = (rop,st') /\ ~is_terminator opc ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> drule emitted_insts_emit_op >> simp[mk_inst_def]
QED

Theorem emitted_void_nonterminators:
  emit_void opc ops st = ((),st') /\ ~is_terminator opc ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> drule emitted_insts_emit_void >> simp[mk_inst_def]
QED

Theorem old_operand_taint_frame:
  (!x. not_fresh_at st x ==> op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  op_taint tn' op = op_taint tn op
Proof
  Cases_on `op` >> simp[op_taint_def]
QED

Theorem state_frame_ptr_fields:
  state_frame t = state_frame s ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests
Proof
  simp[state_frame_def, venom_state_component_equality]
QED
