Theory runtimeSymSrcContextCopy
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmissionProbe runtimeSymSrcEmission
  context compileEnv emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_assign:
  ~is_label_operand op /\ EVERY runtime_sym_inst (state_insts s) /\
  emit_inst ASSIGN [op] [v] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  rpt strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at Any) >> qexists `s.cs_next_id` >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[]
QED

Theorem runtime_sym_copy_offset:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  (if scale = 1 then emit_op ADD [src; Var count_oper]
   else do scaled <- emit_op MUL [Var count_oper; Lit (n2w scale)];
           emit_op ADD [src; scaled] od) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `scale = 1` >> simp[comp_bind_def] >> strip_tac
  >- (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]) >>
  pairarg_tac >> gvs[] >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_copy_new_block:
  EVERY runtime_sym_inst (state_insts s) /\
  new_block lbl s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> mp_tac (Q.INST [`label` |-> `lbl`, `st` |-> `s`] runtime_sym_new_block) >> simp[]
QED

Theorem runtime_sym_word_copy_loop_base:
  ~is_label_operand src /\ ~is_label_operand dst /\
  ~is_label_operand count_op /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_word_copy_loop_base src dst count_op load_loc store_loc ctor imm s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_word_copy_loop_base_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (qpat_x_assum `fresh_label _ _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_label) >> strip_tac) >>
  qpat_x_assum `fresh_var _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_var) >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block cond_lbl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op EQ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block body_lbl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _`
    (mp_then Any mp_tac runtime_sym_copy_offset) >> simp[] >> strip_tac >>
  qpat_x_assum `compile_ptr_load _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_ptr_load) >> simp[] >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _`
    (mp_then Any mp_tac runtime_sym_copy_offset) >> simp[] >> strip_tac >>
  qpat_x_assum `compile_ptr_store _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_ptr_store) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  gvs[] >> drule_all runtime_sym_copy_new_block >> simp[]
QED

Theorem runtime_sym_word_copy_loop_op:
  ~is_label_operand src /\ ~is_label_operand dst /\
  ~is_label_operand count_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_word_copy_loop_op src dst count_op ll sl ctor s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_word_copy_loop_op_def] >> strip_tac >>
  qpat_assum `compile_word_copy_loop_base _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_word_copy_loop_base) >> simp[]
QED

Theorem runtime_sym_word_copy_loop:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_word_copy_loop src dst n ll sl ctor s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_word_copy_loop_def] >> strip_tac >>
  qpat_assum `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_word_copy_loop_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_storage_to_memory:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_storage_to_memory src dst n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_storage_to_memory_def] >>
  metis_tac[runtime_sym_word_copy_loop]
QED

Theorem runtime_sym_memory_to_storage:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_memory_to_storage src dst n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_memory_to_storage_def] >>
  metis_tac[runtime_sym_word_copy_loop]
QED

Theorem runtime_sym_transient_to_memory:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_transient_to_memory src dst n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_transient_to_memory_def] >>
  metis_tac[runtime_sym_word_copy_loop]
QED

Theorem runtime_sym_memory_to_transient:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_memory_to_transient src dst n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_memory_to_transient_def] >>
  metis_tac[runtime_sym_word_copy_loop]
QED

Theorem runtime_sym_slot_to_memory:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_slot_to_memory src dst n loc s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_slot_to_memory_def] >>
  metis_tac[runtime_sym_word_copy_loop]
QED

Theorem runtime_sym_code_to_memory:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_code_to_memory src dst n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `n = 0` >>
  simp[compile_code_to_memory_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_word_copy_loop >> simp[]
QED

Theorem runtime_sym_ensure_in_memory:
  ~is_label_operand ptr_op /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ensure_in_memory ptr_op loc mem_bytes n ctor imm s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `loc`
  >- (simp[compile_ensure_in_memory_def, comp_return_def] >> strip_tac >> gvs[]) >>
  Cases_on `n = 1` >>
  simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `compile_alloc_buffer _ _ = _`
      (mp_then Any mp_tac runtime_sym_alloc_buffer),
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `compile_storage_to_memory _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_storage_to_memory),
    qpat_x_assum `compile_transient_to_memory _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_transient_to_memory),
    qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_imm_copy_to_memory)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_load_storage:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_load_storage src prim n sz s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_storage_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `compile_alloc_buffer _ _ = _`
      (mp_then Any mp_tac runtime_sym_alloc_buffer),
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `compile_storage_to_memory _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_storage_to_memory)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_load_transient:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_load_transient src prim n sz s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_transient_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `compile_alloc_buffer _ _ = _`
      (mp_then Any mp_tac runtime_sym_alloc_buffer),
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `compile_transient_to_memory _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_transient_to_memory)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_load_immutable:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_load_immutable src prim n sz ctor s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `prim` >> Cases_on `ctor` >>
  simp[compile_load_immutable_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `compile_alloc_buffer _ _ = _`
      (mp_then Any mp_tac runtime_sym_alloc_buffer),
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `compile_code_to_memory _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_code_to_memory)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_load_calldata:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_load_calldata src prim n sz s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_calldata_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `compile_alloc_buffer _ _ = _`
      (mp_then Any mp_tac runtime_sym_alloc_buffer),
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_store_storage:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_storage src dst prim n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_store_storage_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `compile_memory_to_storage _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_memory_to_storage)] >>
    simp[] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_store_transient:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_transient src dst prim n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_store_transient_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `compile_memory_to_transient _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_memory_to_transient)] >>
    simp[] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_store_immutable:
  ~is_label_operand src /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_immutable imm src off n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_store_immutable_def] >> strip_tac >>
  qpat_assum `compile_imm_store_words _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_imm_store_words) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_zero_memory_loop:
  !ptr_op i n s u s'.
  ~is_label_operand ptr_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_zero_memory_loop ptr_op i n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  recInduct compile_zero_memory_loop_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_zero_memory_loop _ _ _ _ = _` mp_tac >>
  Cases_on `i >= words`
  >- (simp[Once compile_zero_memory_loop_def, comp_return_def] >> strip_tac >> gvs[]) >>
  simp[Once compile_zero_memory_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `i = 0` >> simp[comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (FIRST [
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem runtime_sym_zero_memory:
  ~is_label_operand ptr_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_zero_memory ptr_op sz s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `sz` >> simp[compile_zero_memory_def, comp_return_def]
  >- (strip_tac >> gvs[]) >> metis_tac[runtime_sym_zero_memory_loop]
QED

Theorem runtime_sym_dynarray_to_storage:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_dynarray_to_storage src dst ew em transient s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `ew = 1` >> Cases_on `transient` >>
  simp[compile_dynarray_to_storage_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (FIRST [
    qpat_x_assum `fresh_label _ _ = _`
      (mp_then Any mp_tac runtime_sym_fresh_label),
    qpat_x_assum `fresh_var _ = _`
      (mp_then Any mp_tac runtime_sym_fresh_var)] >> strip_tac) >> gvs[] >>
  rpt (FIRST [
    qpat_x_assum `emit_op _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op),
    qpat_x_assum `emit_void _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_void),
    qpat_x_assum `emit_inst ASSIGN [_] [_] _ = _`
      (mp_then Any mp_tac runtime_sym_assign),
    qpat_x_assum `emit_inst JMP _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_jump),
    qpat_x_assum `emit_inst JNZ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_jnz),
    qpat_x_assum `new_block _ _ = _`
      (mp_then Any mp_tac runtime_sym_copy_new_block),
    qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_word_copy_loop)] >>
    simp[is_label_operand_def] >> strip_tac) >> gvs[]
QED

Theorem runtime_sym_store_immutable_bytestring:
  ~is_label_operand src /\ ~is_label_operand dst /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_immutable_bytestring imm src dst s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qpat_assum `compile_bytestring_word_count _ _ = _`
    (mp_then Any mp_tac runtime_sym_bytestring_word_count) >> simp[] >> strip_tac >>
  qpat_assum `compile_word_copy_loop_base _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_word_copy_loop_base) >> simp[]
QED
