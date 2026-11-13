(* Primitive execution phases with their S3 endpoint frames. *)
Theory abiEncoderWindowPhaseFrameMem
Ancestors
  abiEncoderWindowLoadMemoryMem
  abiEncoderWindowSequenceFrameMem abiEncoderWindowMemFrame windowPhaseMem
  stmtReasonLitFragMemory abiDecoderVarSequence
  abiEncoderWindowSequence emitHelperProps fragExec list rich_list
  venomInst venomState venomExecSemantics emitHelper exprLoweringProps instMemFrontier
  allocaFootprint windowSequenceMem abiEncoderWindowPhase abiEncoderWindowCursor
  abiEncoderWindowLeaves abiEncoderRegisteredEffect abiEncoderPrimitiveEffect pred_set

Theorem window_emit_op_seq_frame[local]:
  emit_op opc ops st = (out,en) /\ window_seq st en s raw /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\ alloca_inv s /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (abi_decoder_reentry_opcode opc \/
   MEM opc [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP]) ==>
  window_mem_frame ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_seq_mem_frame >> simp[] >> qexists `st` >>
  simp[] >> drule emitted_insts_emit_op >> simp[mk_inst_def] >> gvs[]
QED

Theorem window_emit_add_phase_mem_frame_memory:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  `t.vs_memory = s.vs_memory` by fs[window_pure_seq_def] >>
  `window_seq st en s t` by fs[window_pure_seq_def] >>
  `window_mem_frame ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_emit_op_seq_frame >> goal_assum (drule_at Any) >>
     simp[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_op_mem_ok >> disch_then irule >> simp[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  qexists `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_emit_add_phase_mem_frame:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all window_emit_add_phase_mem_frame_memory >>
  strip_tac >> qexists `t` >> asm_rewrite_tac[]
QED

Theorem window_cursor_load_phase_mem_frame:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  b+32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all window_cursor_load_phase_memory_mem >>
  strip_tac >> qexists `t` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_emit_alloca32_phase_mem_frame:
  emit_op ALLOCA [Lit 32w] st = (out,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    eval_operand out t = SOME (n2w b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ mem_cont_sim ctx func s t /\
    window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  `window_mem_frame ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_emit_op_seq_frame >> goal_assum (drule_at Any) >>
     simp[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_op_mem_ok >> disch_then irule >> simp[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  qexistsl [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  (conj_tac >- metis_tac[window_seq_phase]) >>
  simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  `t.vs_labels = s.vs_labels` by metis_tac[window_seq_labels] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_store_phase_mem_frame:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_registered_effect ids outs s (mstore b w s) /\
  fn_inst_ids_distinct func ==>
  window_phase ctx func st en ids outs s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  window_mem_frame ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> (conj_tac >- metis_tac[window_store_phase_mem]) >>
  (conj_tac >- metis_tac[window_store_phase_mem]) >>
  drule_all window_emit_store_run >> strip_tac >>
  `en.cs_next_var = st.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `window_seq st en s (mstore b w s)` by
    (simp[window_seq_def] >>
     simp_tac (srw_ss()) [lookup_var_def, mstore_def,
       write_memory_with_expansion_def]) >>
  irule window_seq_mem_frame >> simp[] >> qexists `st` >> simp[] >>
  drule emitted_insts_emit_void >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem window_cursor_store_phase_mem_frame:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas id = SOME (b,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  window_phase ctx func st en {id} [] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  window_mem_frame ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase_mem_frame >> simp[] >>
  metis_tac[abi_encoder_registered_slot_store, IN_SING]
QED

Theorem window_output_store_phase_mem_frame:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  window_phase ctx func st en {} [(b,32)] s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  mem_cont_sim ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts) /\
  window_mem_frame ctx func s
    ((mstore b w s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> irule window_store_phase_mem_frame >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  irule abi_encoder_output_store >> simp[]
QED

Theorem window_emit_add_phase_mem_conditional_frame_memory:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t) /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >> Cases_on `fn_inst_ids_distinct func`
  >- (drule_all window_emit_add_phase_mem_frame_memory >> metis_tac[]) >>
  drule_all window_emit_add_phase_mem_memory >> metis_tac[]
QED

Theorem window_emit_add_phase_mem_conditional_frame:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >> drule_all window_emit_add_phase_mem_conditional_frame_memory >>
  strip_tac >> qexists `t` >> asm_rewrite_tac[]
QED

Theorem window_cursor_load_phase_mem_conditional_frame:
  emit_op MLOAD [ptr_op] st = (out,en) /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) /\
  b+32 <= s.vs_alloca_next /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >> Cases_on `fn_inst_ids_distinct func`
  >- (drule_all window_cursor_load_phase_mem_frame >> metis_tac[]) >>
  drule_all window_cursor_load_phase_mem >> metis_tac[]
QED

Theorem window_emit_alloca32_phase_mem_conditional_frame:
  emit_op ALLOCA [Lit 32w] st = (out,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    eval_operand out t = SOME (n2w b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >> Cases_on `fn_inst_ids_distinct func`
  >- (drule_all window_emit_alloca32_phase_mem_frame >> metis_tac[]) >>
  drule_all window_emit_alloca32_phase_mem >> metis_tac[]
QED
